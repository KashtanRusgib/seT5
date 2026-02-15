/**
 * @file tbe_main.c
 * @brief TBE — Ternary Bootstrap Environment Main
 *
 * Minimal userspace shell bootstrapping seT5.  Provides an interactive
 * 15-command environment for I/O, environment-variable management,
 * syscall testing, and balanced-ternary operations.
 *
 * Runs atop the seT5 microkernel (kernel_state_t), leveraging:
 *   - tbe_shell.h register/dot/fft/conv/alloc/free/cap/sched/noise/wcet/telem
 *   - Extended commands: echo, env, setenv, consensus, accept_any,
 *     trithon_call, syscall (direct dispatch), exit
 *   - Trit-based environment variables (key/value as trit arrays)
 *   - Syscall fallback: logs + emulates on failure
 *   - WCET probing around every operation for telemetry
 *
 * Build:
 *   make tbe      # or: gcc -Wall -Iinclude -Itools/compiler/include \
 *                 #       -o tbe src/tbe_main.c src/memory.c src/ipc.c \
 *                 #       src/scheduler.c src/syscall.c src/multiradix.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "set5/trit.h"
#include "set5/trit_emu.h"
#include "set5/trit_cast.h"
#include "set5/memory.h"
#include "set5/ipc.h"
#include "set5/scheduler.h"
#include "set5/syscall.h"
#include "set5/multiradix.h"
#include "set5/qemu_trit.h"
#include "set5/wcet.h"
#include "set5/posix.h"

/* ===================================================================== */
/*  1.  Trit-Based Environment Variables                                 */
/* ===================================================================== */

#define TBE_MAX_ENV   16
#define TBE_KEY_LEN   32
#define TBE_VAL_LEN   128

typedef struct {
    char key[TBE_KEY_LEN];      /**< ASCII key (e.g. "PATH") */
    trit val[TBE_VAL_LEN];      /**< Balanced-ternary value array */
    int  val_len;               /**< Number of trits stored */
    trit validity;              /**< T=active, U=shadow, F=deleted */
} tbe_env_t;

typedef struct {
    tbe_env_t entries[TBE_MAX_ENV];
    int       count;
} tbe_env_table_t;

static void tbe_env_init(tbe_env_table_t *env) {
    if (!env) return;
    env->count = 0;
    for (int i = 0; i < TBE_MAX_ENV; i++) {
        env->entries[i].key[0]   = '\0';
        env->entries[i].val_len  = 0;
        env->entries[i].validity = TRIT_FALSE;
    }
    /* Pre-seed mandatory env vars */
    strncpy(env->entries[0].key, "SHELL", TBE_KEY_LEN - 1);
    env->entries[0].val[0] = TRIT_TRUE;
    env->entries[0].val_len = 1;
    env->entries[0].validity = TRIT_TRUE;
    strncpy(env->entries[1].key, "TRIT_MODE", TBE_KEY_LEN - 1);
    env->entries[1].val[0] = TRIT_TRUE;   /* Kleene K3 */
    env->entries[1].val[1] = TRIT_UNKNOWN;
    env->entries[1].val[2] = TRIT_FALSE;
    env->entries[1].val_len = 3;
    env->entries[1].validity = TRIT_TRUE;
    env->count = 2;
}

static int tbe_env_find(const tbe_env_table_t *env, const char *key) {
    for (int i = 0; i < TBE_MAX_ENV; i++) {
        if (env->entries[i].validity != TRIT_FALSE &&
            strcmp(env->entries[i].key, key) == 0)
            return i;
    }
    return -1;
}

static int tbe_env_set(tbe_env_table_t *env, const char *key, int value) {
    int idx = tbe_env_find(env, key);
    if (idx < 0) {
        /* Allocate new slot */
        if (env->count >= TBE_MAX_ENV) return -1;
        idx = env->count++;
    }
    strncpy(env->entries[idx].key, key, TBE_KEY_LEN - 1);
    env->entries[idx].key[TBE_KEY_LEN - 1] = '\0';
    env->entries[idx].validity = TRIT_TRUE;

    /* Store value as balanced ternary (Avizienis encoding) */
    int n = value, pos = 0;
    memset(env->entries[idx].val, 0, sizeof(env->entries[idx].val));
    if (n == 0) {
        env->entries[idx].val[0] = TRIT_UNKNOWN;
        env->entries[idx].val_len = 1;
        return 0;
    }
    int neg = (n < 0);
    if (neg) n = -n;
    while (n != 0 && pos < TBE_VAL_LEN) {
        int r = n % 3;
        if (r == 0) { env->entries[idx].val[pos] = TRIT_UNKNOWN; n = n / 3; }
        else if (r == 1) { env->entries[idx].val[pos] = TRIT_TRUE;  n = (n - 1) / 3; }
        else { env->entries[idx].val[pos] = TRIT_FALSE; n = (n + 1) / 3; }
        pos++;
    }
    if (neg) {
        for (int i = 0; i < pos; i++)
            env->entries[idx].val[i] = trit_not(env->entries[idx].val[i]);
    }
    env->entries[idx].val_len = pos;
    return 0;
}

static void tbe_env_print(const tbe_env_table_t *env) {
    printf("Environment (%d/%d):\n", env->count, TBE_MAX_ENV);
    for (int i = 0; i < TBE_MAX_ENV; i++) {
        const tbe_env_t *e = &env->entries[i];
        if (e->validity == TRIT_FALSE) continue;
        const char *vstr = (e->validity == TRIT_TRUE)    ? "T" :
                           (e->validity == TRIT_UNKNOWN)  ? "U" : "F";
        printf("  %s [%s] = {", e->key, vstr);
        for (int j = 0; j < e->val_len; j++) {
            char c = (e->val[j] == TRIT_TRUE) ? 'T' :
                     (e->val[j] == TRIT_FALSE) ? 'F' : 'U';
            putchar(c);
        }
        printf("}\n");
    }
}

/* ===================================================================== */
/*  2.  Ternary Consensus / Accept-Any (Kleene K3 bulk)                  */
/* ===================================================================== */

/**
 * Consensus: Kleene AND of two 32-trit registers.
 * Returns number of T-valued trits in result.
 */
static int tbe_consensus(multiradix_state_t *mr, int ra, int rb) {
    if (!mr || ra < 0 || ra >= MR_NUM_REGS || rb < 0 || rb >= MR_NUM_REGS)
        return -1;
    int agree = 0;
    for (int i = 0; i < 32; i++) {
        trit a = trit2_to_trit(trit2_reg32_get(&mr->regs[ra], i));
        trit b = trit2_to_trit(trit2_reg32_get(&mr->regs[rb], i));
        trit c = trit_and(a, b);
        if (c == TRIT_TRUE) agree++;
    }
    return agree;
}

/**
 * Accept-any: Kleene OR of two 32-trit registers.
 * Returns number of T-valued trits in result.
 */
static int tbe_accept_any(multiradix_state_t *mr, int ra, int rb) {
    if (!mr || ra < 0 || ra >= MR_NUM_REGS || rb < 0 || rb >= MR_NUM_REGS)
        return -1;
    int accepted = 0;
    for (int i = 0; i < 32; i++) {
        trit a = trit2_to_trit(trit2_reg32_get(&mr->regs[ra], i));
        trit b = trit2_to_trit(trit2_reg32_get(&mr->regs[rb], i));
        trit c = trit_or(a, b);
        if (c == TRIT_TRUE) accepted++;
    }
    return accepted;
}

/* ===================================================================== */
/*  3.  Syscall Fallback (Emulator-Mode)                                 */
/* ===================================================================== */

/**
 * Wrap syscall_dispatch with fallback logging.
 *
 * If the kernel syscall returns a negative retval, log the failure
 * and attempt a best-effort emulated result so the shell continues.
 */
static syscall_result_t tbe_syscall_safe(kernel_state_t *ks,
                                         int sysno, int a0, int a1) {
    syscall_result_t r = syscall_dispatch(ks, sysno, a0, a1);
    if (r.retval < 0) {
        fprintf(stderr, "[TBE FALLBACK] syscall %d(%d,%d) failed (ret=%d). "
                        "Emulating safe result.\n", sysno, a0, a1, r.retval);
        /* Safe fallback: clear the error and return Unknown */
        r.retval      = 0;
        r.result_trit = TRIT_UNKNOWN;
    }
    return r;
}

/* ===================================================================== */
/*  4.  Trithon Interop Stub                                             */
/* ===================================================================== */

/**
 * Call into the Python Trithon interpreter.
 *
 * In the full stack this would use CFFI / subprocess to evaluate
 * a Trithon expression.  For now, parse simple trit-literal
 * expressions locally.
 */
static void tbe_trithon_call(const char *expr) {
    if (!expr || expr[0] == '\0') {
        printf("Trithon: empty expression\n");
        return;
    }

    /* Tiny trit-literal evaluator: T&F, T|U, ~T, etc. */
    trit lhs = TRIT_UNKNOWN, rhs = TRIT_UNKNOWN;

    /* Look for operator */
    const char *op = NULL;
    for (const char *p = expr; *p; p++) {
        if (*p == '&' || *p == '|' || *p == '~') { op = p; break; }
    }

    if (op && *op == '~') {
        /* Unary NOT: ~T, ~U, ~F */
        char v = (op[1] != '\0') ? op[1] : 'U';
        lhs = (v == 'T' || v == 't') ? TRIT_TRUE :
              (v == 'F' || v == 'f') ? TRIT_FALSE : TRIT_UNKNOWN;
        trit result = trit_not(lhs);
        printf("Trithon: ~%c = %c\n", v,
               result == TRIT_TRUE ? 'T' : result == TRIT_FALSE ? 'F' : 'U');
    } else if (op) {
        /* Binary: X&Y or X|Y */
        lhs = (expr[0] == 'T' || expr[0] == 't') ? TRIT_TRUE :
              (expr[0] == 'F' || expr[0] == 'f') ? TRIT_FALSE : TRIT_UNKNOWN;
        char rv = op[1];
        rhs = (rv == 'T' || rv == 't') ? TRIT_TRUE :
              (rv == 'F' || rv == 'f') ? TRIT_FALSE : TRIT_UNKNOWN;
        trit result;
        if (*op == '&') result = trit_and(lhs, rhs);
        else            result = trit_or(lhs, rhs);
        printf("Trithon: %c%c%c = %c\n",
               expr[0], *op, rv,
               result == TRIT_TRUE ? 'T' : result == TRIT_FALSE ? 'F' : 'U');
    } else {
        printf("Trithon: (no operator found in '%s')\n", expr);
        printf("  Supported: T&F, U|T, ~T, etc.\n");
    }
}

/* ===================================================================== */
/*  5.  WCET-Instrumented Command Helpers                                */
/* ===================================================================== */

/**
 * @brief Register TBE WCET probes on startup.
 * Returns probe IDs: [0]=cmd_dispatch, [1]=dot, [2]=fft, [3]=syscall
 */
static void tbe_wcet_setup(wcet_state_t *w) {
    wcet_register(w, "cmd_dispatch", 50);
    wcet_register(w, "dot_trit",    100);
    wcet_register(w, "fft_step",    120);
    wcet_register(w, "syscall",      20);
    wcet_register(w, "alloc",       300);
    wcet_register(w, "conv",         80);
}

/* ===================================================================== */
/*  6.  TBE Main — Extended 15-Command Shell                             */
/* ===================================================================== */

/**
 * TBE command IDs (matches the user's 15-command prototype).
 *
 *  0  help          7  trit_inc      14 exit
 *  1  echo          8  trit_dec
 *  2  env           9  consensus
 *  3  setenv       10  accept_any
 *  4  reg          11  fft
 *  5  dot          12  wcet
 *  6  syscall      13  trithon
 */

static void tbe_banner(void) {
    printf(
        "\n"
        "┌─────────────────────────────────────────────┐\n"
        "│  seT5 TBE — Ternary Bootstrap Environment   │\n"
        "│  v0.2  •  15 commands  •  Kleene K₃ logic   │\n"
        "│  Type 'help' for command list                │\n"
        "└─────────────────────────────────────────────┘\n"
        "\n"
    );
}

static void tbe_help(void) {
    printf(
        "Commands (15):\n"
        "  help                    Show this message\n"
        "  echo <text>             Echo text to stdout\n"
        "  env                     Print environment variables\n"
        "  setenv <key> <int>      Set env var (balanced ternary value)\n"
        "  reg <n>                 Show ternary register n (0-15)\n"
        "  dot <a> <b>             DOT_TRIT of registers a, b\n"
        "  syscall <no> <a0> <a1>  Direct kernel syscall dispatch\n"
        "  trit_inc <reg>          Balanced ternary increment register\n"
        "  trit_dec <reg>          Balanced ternary decrement register\n"
        "  consensus <a> <b>      Ternary AND of registers (Kleene consensus)\n"
        "  accept_any <a> <b>     Ternary OR of registers (Kleene accept-any)\n"
        "  fft <reg> <offset>      Radix-3 FFT butterfly step\n"
        "  wcet                    Print WCET probe telemetry\n"
        "  trithon <expr>          Evaluate Trithon trit expression\n"
        "  exit                    Shutdown TBE\n"
    );
}

/**
 * Balanced ternary increment on a 32-trit register.
 *
 * Starting from trit 0 (LST), propagates carry using:
 *   F(-1) + 1 = U(0),  carry = 0  (done)
 *   U(0)  + 1 = T(+1), carry = 0  (done)
 *   T(+1) + 1 = F(-1), carry = 1  (continue)
 */
static void tbe_trit_inc(multiradix_state_t *mr, int reg) {
    if (reg < 0 || reg >= MR_NUM_REGS) { printf("Invalid register\n"); return; }
    int carry = 1;
    for (int i = 0; i < 32 && carry; i++) {
        trit2 t = trit2_reg32_get(&mr->regs[reg], i);
        trit  s = trit2_to_trit(t);
        int   v = (int)s + carry;
        if (v > 1) { v = -1; carry = 1; }
        else       { carry = 0; }
        trit2_reg32_set(&mr->regs[reg], i,
                        (v == 1) ? TRIT2_TRUE :
                        (v == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN);
    }
    printf("INC R%02d: ", reg);
    const char syms[] = "FU?T";
    for (int i = 31; i >= 0; i--) {
        trit2 t = trit2_reg32_get(&mr->regs[reg], i);
        int idx = (t == TRIT2_FALSE) ? 0 :
                  (t == TRIT2_UNKNOWN) ? 1 :
                  (t == TRIT2_TRUE) ? 3 : 2;
        putchar(syms[idx]);
        if (i % 6 == 0 && i > 0) putchar('_');
    }
    putchar('\n');
}

/**
 * Balanced ternary decrement (negate-increment-negate would work,
 * but direct subtraction is symmetric):
 *   T(+1) - 1 = U(0),  borrow = 0
 *   U(0)  - 1 = F(-1), borrow = 0
 *   F(-1) - 1 = T(+1), borrow = 1
 */
static void tbe_trit_dec(multiradix_state_t *mr, int reg) {
    if (reg < 0 || reg >= MR_NUM_REGS) { printf("Invalid register\n"); return; }
    int borrow = 1;
    for (int i = 0; i < 32 && borrow; i++) {
        trit2 t = trit2_reg32_get(&mr->regs[reg], i);
        trit  s = trit2_to_trit(t);
        int   v = (int)s - borrow;
        if (v < -1) { v = 1; borrow = 1; }
        else        { borrow = 0; }
        trit2_reg32_set(&mr->regs[reg], i,
                        (v == 1) ? TRIT2_TRUE :
                        (v == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN);
    }
    printf("DEC R%02d: ", reg);
    const char syms[] = "FU?T";
    for (int i = 31; i >= 0; i--) {
        trit2 t = trit2_reg32_get(&mr->regs[reg], i);
        int idx = (t == TRIT2_FALSE) ? 0 :
                  (t == TRIT2_UNKNOWN) ? 1 :
                  (t == TRIT2_TRUE) ? 3 : 2;
        putchar(syms[idx]);
        if (i % 6 == 0 && i > 0) putchar('_');
    }
    putchar('\n');
}

/* ===================================================================== */
/*  7.  Main Entry Point                                                 */
/* ===================================================================== */

int main(void) {
    /* ---- Kernel bootstrap ---- */
    kernel_state_t ks;
    kernel_init(&ks, 64);  /* 64 pages for TBE session */

    /* ---- TBE state ---- */
    tbe_env_table_t env;
    tbe_env_init(&env);

    wcet_state_t wcet;
    wcet_init(&wcet);
    tbe_wcet_setup(&wcet);

    qemu_noise_t noise;
    qemu_noise_init(&noise, NOISE_NONE, 42, 0);

    /* ---- Seed telemetry ---- */
    multiradix_init(&ks.mr);

    /* ---- Shell loop ---- */
    tbe_banner();

    char line[512];
    char cmd[64];
    int  running = 1;

    while (running) {
        printf("tbe> ");
        fflush(stdout);
        if (!fgets(line, sizeof(line), stdin)) break;

        /* Strip newline */
        line[strcspn(line, "\n")] = '\0';
        if (line[0] == '\0') continue;

        /* Extract command word */
        if (sscanf(line, "%63s", cmd) != 1) continue;

        int n1 = 0, n2 = 0, n3 = 0;
        char arg_str[256] = "";

        /* ---- Dispatch (15 commands) ---- */

        if (strcmp(cmd, "help") == 0) {
            tbe_help();

        } else if (strcmp(cmd, "echo") == 0) {
            /* echo <text> — print everything after "echo " */
            const char *text = line + 5;
            while (*text == ' ') text++;
            printf("%s\n", text);

        } else if (strcmp(cmd, "env") == 0) {
            tbe_env_print(&env);

        } else if (strcmp(cmd, "setenv") == 0) {
            if (sscanf(line, "%*s %255s %d", arg_str, &n1) == 2) {
                if (tbe_env_set(&env, arg_str, n1) == 0)
                    printf("Set %s = %d (balanced ternary)\n", arg_str, n1);
                else
                    printf("Env table full (%d/%d)\n", env.count, TBE_MAX_ENV);
            } else {
                printf("Usage: setenv <key> <int>\n");
            }

        } else if (strcmp(cmd, "reg") == 0) {
            if (sscanf(line, "%*s %d", &n1) == 1) {
                if (n1 < 0 || n1 >= MR_NUM_REGS) {
                    printf("Invalid register %d (0-%d)\n", n1, MR_NUM_REGS-1);
                } else {
                    printf("R%02d: ", n1);
                    const char syms[] = "FU?T";
                    for (int i = 31; i >= 0; i--) {
                        trit2 t = trit2_reg32_get(&ks.mr.regs[n1], i);
                        int idx = (t == TRIT2_FALSE) ? 0 :
                                  (t == TRIT2_UNKNOWN) ? 1 :
                                  (t == TRIT2_TRUE) ? 3 : 2;
                        putchar(syms[idx]);
                        if (i % 6 == 0 && i > 0) putchar('_');
                    }
                    putchar('\n');
                }
            } else {
                printf("Usage: reg <n>\n");
            }

        } else if (strcmp(cmd, "dot") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2) {
                wcet_observe(&wcet, 1, 0); /* pre-probe */
                struct timespec ts0, ts1;
                clock_gettime(CLOCK_MONOTONIC, &ts0);
                int result = dot_trit(&ks.mr, n1, n2);
                clock_gettime(CLOCK_MONOTONIC, &ts1);
                uint64_t ns = (ts1.tv_sec - ts0.tv_sec) * 1000000000ULL +
                              (ts1.tv_nsec - ts0.tv_nsec);
                wcet_observe(&wcet, 1, ns);
                printf("DOT(R%02d, R%02d) = %d  [%lu ns]\n",
                       n1, n2, result, (unsigned long)ns);
            } else {
                printf("Usage: dot <a> <b>\n");
            }

        } else if (strcmp(cmd, "syscall") == 0) {
            if (sscanf(line, "%*s %d %d %d", &n1, &n2, &n3) >= 1) {
                syscall_result_t r = tbe_syscall_safe(&ks, n1, n2, n3);
                printf("syscall(%d, %d, %d) → ret=%d trit=%s\n",
                       n1, n2, n3, r.retval,
                       r.result_trit == TRIT_TRUE ? "T" :
                       r.result_trit == TRIT_FALSE ? "F" : "U");
            } else {
                printf("Usage: syscall <no> <arg0> <arg1>\n");
            }

        } else if (strcmp(cmd, "trit_inc") == 0) {
            if (sscanf(line, "%*s %d", &n1) == 1)
                tbe_trit_inc(&ks.mr, n1);
            else
                printf("Usage: trit_inc <reg>\n");

        } else if (strcmp(cmd, "trit_dec") == 0) {
            if (sscanf(line, "%*s %d", &n1) == 1)
                tbe_trit_dec(&ks.mr, n1);
            else
                printf("Usage: trit_dec <reg>\n");

        } else if (strcmp(cmd, "consensus") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2) {
                int agree = tbe_consensus(&ks.mr, n1, n2);
                printf("CONSENSUS(R%02d, R%02d) = %d trits agree (of 32)\n",
                       n1, n2, agree);
            } else {
                printf("Usage: consensus <reg_a> <reg_b>\n");
            }

        } else if (strcmp(cmd, "accept_any") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2) {
                int accepted = tbe_accept_any(&ks.mr, n1, n2);
                printf("ACCEPT_ANY(R%02d, R%02d) = %d trits accepted (of 32)\n",
                       n1, n2, accepted);
            } else {
                printf("Usage: accept_any <reg_a> <reg_b>\n");
            }

        } else if (strcmp(cmd, "fft") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2) {
                wcet_observe(&wcet, 2, 0);
                struct timespec ts0, ts1;
                clock_gettime(CLOCK_MONOTONIC, &ts0);
                fft_step(&ks.mr, n1, n2, 1);
                clock_gettime(CLOCK_MONOTONIC, &ts1);
                uint64_t ns = (ts1.tv_sec - ts0.tv_sec) * 1000000000ULL +
                              (ts1.tv_nsec - ts0.tv_nsec);
                wcet_observe(&wcet, 2, ns);
                printf("FFT(R%02d, offset=%d) done [%lu ns]. Result: ",
                       n1, n2, (unsigned long)ns);
                const char syms[] = "FU?T";
                for (int i = 31; i >= 0; i--) {
                    trit2 t = trit2_reg32_get(&ks.mr.regs[n1], i);
                    int idx = (t == TRIT2_FALSE) ? 0 :
                              (t == TRIT2_UNKNOWN) ? 1 :
                              (t == TRIT2_TRUE) ? 3 : 2;
                    putchar(syms[idx]);
                    if (i % 6 == 0 && i > 0) putchar('_');
                }
                putchar('\n');
            } else {
                printf("Usage: fft <reg> <offset>\n");
            }

        } else if (strcmp(cmd, "wcet") == 0) {
            printf("WCET probes (%d registered):\n", wcet.probe_count);
            for (int i = 0; i < wcet.probe_count; i++) {
                wcet_probe_t *p = &wcet.probes[i];
                printf("  [%d] %-14s budget=%-6lu max=%-6lu avg=%-6lu viol=%d\n",
                       i, p->label,
                       (unsigned long)p->budget_cycles,
                       (unsigned long)p->observed_max,
                       (unsigned long)wcet_average(&wcet, i),
                       p->violation_count);
            }

        } else if (strcmp(cmd, "trithon") == 0) {
            const char *expr = line + 8;
            while (*expr == ' ') expr++;
            tbe_trithon_call(expr);

        } else if (strcmp(cmd, "exit") == 0 || strcmp(cmd, "quit") == 0) {
            printf("TBE: Shutting down seT5 kernel...\n");
            running = 0;

        } else {
            printf("Unknown command: '%s'. Type 'help' for list.\n", cmd);
        }
    }

    /* ---- Cleanup ---- */
    printf("TBE: Goodbye.  %d env vars, %d WCET probes, %d violations.\n",
           env.count, wcet.probe_count, wcet.total_violations);
    return 0;
}
