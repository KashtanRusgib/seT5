/**
 * @file tbe_shell.h
 * @brief TBE — Ternary Bootstrap Environment Shell
 *
 * A minimal interactive shell for the seT5 microkernel, providing:
 *   - Ternary register inspection and manipulation
 *   - DOT_TRIT, FFT, RADIX_CONV commands
 *   - Memory allocation / free
 *   - Capability creation / inspect
 *   - Scheduler status
 *   - QEMU noise configuration
 *   - WCET telemetry queries
 *
 * Commands:
 *   help                    — Show command list
 *   reg <n>                 — Print register n contents
 *   set <n> <pos> <F|U|T>   — Set trit at position in register
 *   dot <a> <b>             — DOT_TRIT on registers a, b
 *   fft <n> <off>           — FFT butterfly on register n at offset
 *   conv <n> <int>          — RADIX_CONV: load balanced ternary of int
 *   alloc <owner>           — Allocate a memory page
 *   free <page>             — Free a memory page
 *   cap                     — List capability table
 *   sched                   — Scheduler status
 *   noise <model> <ppm>     — Configure QEMU noise model
 *   wcet                    — Print WCET probe status
 *   telem                   — Print TRIT_LB telemetry
 *   quit                    — Exit shell
 *
 * The TBE shell operates on the unified kernel_state_t, so any
 * changes made here affect the running kernel state.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TBE_SHELL_H
#define SET5_TBE_SHELL_H

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "set5/syscall.h"
#include "set5/multiradix.h"
#include "set5/qemu_trit.h"
#include "set5/wcet.h"

/* ---- Shell State ------------------------------------------------------ */

typedef struct {
    kernel_state_t *ks;        /* Kernel state reference */
    qemu_noise_t    noise;     /* Noise simulator */
    wcet_state_t    wcet;      /* WCET probes */
    int             running;   /* Shell loop control */
} tbe_state_t;

static inline void tbe_init(tbe_state_t *tbe, kernel_state_t *ks) {
    if (!tbe) return;
    tbe->ks = ks;
    tbe->running = 1;
    qemu_noise_init(&tbe->noise, NOISE_NONE, 42, 0);
    wcet_init(&tbe->wcet);
}

/* ---- Helper: Print a 32-trit register --------------------------------- */

static inline void tbe_print_reg(const trit2_reg32 *r) {
    const char syms[] = "FU?T"; /* 00=F, 01=U, 10=?, 11=T */
    for (int i = 31; i >= 0; i--) {
        trit2 t = trit2_reg32_get(r, i);
        int idx = (t == TRIT2_FALSE) ? 0 :
                  (t == TRIT2_UNKNOWN) ? 1 :
                  (t == TRIT2_TRUE) ? 3 : 2;
        putchar(syms[idx]);
        if (i % 6 == 0 && i > 0) putchar('_');  /* Tryte boundaries */
    }
    putchar('\n');
}

/* ---- Command Dispatch ------------------------------------------------- */

static inline void tbe_cmd_help(void) {
    printf("TBE — Ternary Bootstrap Environment\n");
    printf("Commands:\n");
    printf("  help                    — This message\n");
    printf("  reg <n>                 — Show register n\n");
    printf("  set <r> <pos> <F|U|T>   — Set trit in register\n");
    printf("  dot <a> <b>             — DOT_TRIT\n");
    printf("  fft <r> <off>           — FFT butterfly\n");
    printf("  conv <r> <int>          — Radix conversion\n");
    printf("  alloc <owner>           — Allocate page\n");
    printf("  free <page>             — Free page\n");
    printf("  cap                     — List capabilities\n");
    printf("  sched                   — Scheduler status\n");
    printf("  noise <none|uni|gauss|mem|cosmic> <ppm>\n");
    printf("  wcet                    — WCET probes\n");
    printf("  telem                   — TRIT_LB telemetry\n");
    printf("  quit                    — Exit shell\n");
}

static inline void tbe_cmd_reg(tbe_state_t *tbe, int n) {
    if (n < 0 || n >= MR_NUM_REGS) {
        printf("Invalid register %d (0-%d)\n", n, MR_NUM_REGS - 1);
        return;
    }
    printf("R%02d: ", n);
    tbe_print_reg(&tbe->ks->mr.regs[n]);
}

static inline void tbe_cmd_set(tbe_state_t *tbe, int r, int pos, char val) {
    if (r < 0 || r >= MR_NUM_REGS || pos < 0 || pos >= 32) {
        printf("Invalid register %d or position %d\n", r, pos);
        return;
    }
    trit2 t;
    switch (val) {
        case 'F': case 'f': t = TRIT2_FALSE; break;
        case 'U': case 'u': t = TRIT2_UNKNOWN; break;
        case 'T': case 't': t = TRIT2_TRUE; break;
        default: printf("Invalid trit value '%c'\n", val); return;
    }
    trit2_reg32_set(&tbe->ks->mr.regs[r], pos, t);
    printf("R%02d[%d] = %c\n", r, pos, val);
}

static inline void tbe_cmd_dot(tbe_state_t *tbe, int a, int b) {
    if (a < 0 || a >= MR_NUM_REGS || b < 0 || b >= MR_NUM_REGS) {
        printf("Invalid registers\n");
        return;
    }
    int result = dot_trit(&tbe->ks->mr, a, b);
    printf("DOT(R%02d, R%02d) = %d\n", a, b, result);
}

static inline void tbe_cmd_fft(tbe_state_t *tbe, int r, int off) {
    if (r < 0 || r >= MR_NUM_REGS) { printf("Invalid register\n"); return; }
    fft_step(&tbe->ks->mr, r, off, 1);
    printf("FFT(R%02d, offset=%d) done. Result: ", r, off);
    tbe_print_reg(&tbe->ks->mr.regs[r]);
}

static inline void tbe_cmd_conv(tbe_state_t *tbe, int r, int val) {
    if (r < 0 || r >= MR_NUM_REGS) { printf("Invalid register\n"); return; }
    radix_conv_to_ternary(&tbe->ks->mr, r, val);
    printf("CONV(%d) → R%02d: ", val, r);
    tbe_print_reg(&tbe->ks->mr.regs[r]);
}

static inline void tbe_cmd_alloc(tbe_state_t *tbe, int owner) {
    int page = mem_alloc(&tbe->ks->mem, owner);
    if (page < 0) printf("Allocation failed\n");
    else printf("Allocated page %d for owner %d\n", page, owner);
}

static inline void tbe_cmd_free(tbe_state_t *tbe, int page) {
    mem_free(&tbe->ks->mem, page);
    printf("Freed page %d\n", page);
}

static inline void tbe_cmd_cap(tbe_state_t *tbe) {
    printf("Capability table (%d/%d slots):\n",
           tbe->ks->cap_count, SYSCALL_MAX_CAPS);
    for (int i = 0; i < tbe->ks->cap_count && i < 16; i++) {
        syscall_cap_t *c = &tbe->ks->caps[i];
        const char *v = (c->valid == TRIT_TRUE)  ? "T(active)" :
                       (c->valid == TRIT_UNKNOWN) ? "U(pending)" :
                                                       "F(revoked)";
        printf("  [%2d] obj=%d rights=%d validity=%s\n",
               i, c->object_id, c->rights, v);
    }
}

static inline void tbe_cmd_sched(tbe_state_t *tbe) {
    sched_state_t_state *s = &tbe->ks->sched;
    printf("Scheduler: %d threads, current=%d\n",
           s->thread_count, s->current_tid);
    for (int t = 0; t < s->thread_count && t < 16; t++) {
        const char *states[] = {"READY", "BLOCKED", "DEAD", "RUNNING"};
        int si = s->threads[t].state;
        printf("  [%d] state=%s prio=%d\n",
               t, (si >= 0 && si <= 3) ? states[si] : "?",
               s->threads[t].priority);
    }
}

static inline void tbe_cmd_noise(tbe_state_t *tbe, const char *model, int ppm) {
    noise_model_t m = NOISE_NONE;
    if (strcmp(model, "uni") == 0)     m = NOISE_UNIFORM;
    else if (strcmp(model, "gauss") == 0) m = NOISE_GAUSSIAN;
    else if (strcmp(model, "mem") == 0)   m = NOISE_MEMRISTIVE;
    else if (strcmp(model, "cosmic") == 0) m = NOISE_COSMIC;
    qemu_noise_init(&tbe->noise, m, 42, ppm);
    printf("Noise model: %s, probability: %d ppm\n", model, ppm);
}

static inline void tbe_cmd_wcet(tbe_state_t *tbe) {
    printf("WCET probes (%d registered):\n", tbe->wcet.probe_count);
    for (int i = 0; i < (int)tbe->wcet.probe_count; i++) {
        wcet_probe_t *p = &tbe->wcet.probes[i];
        printf("  [%d] %s: budget=%lu max=%lu avg=%lu violations=%d\n",
               i, p->label, (unsigned long)p->budget_cycles,
               (unsigned long)p->observed_max,
               (unsigned long)wcet_average(&tbe->wcet, i),
               p->violation_count);
    }
}

static inline void tbe_cmd_telem(tbe_state_t *tbe) {
    trit_lb_snapshot_t ss = trit_lb_snapshot(&tbe->ks->mr);
    printf("TRIT_LB Telemetry:\n");
    printf("  Total instructions: %d\n", ss.total_insns);
    printf("  Trit ratio:         %d%%\n", ss.trit_ratio_pct);
    printf("  Sparse ratio:       %d%%\n", ss.sparse_ratio_pct);
    printf("  Thermal events:     %d\n", ss.thermal_events);
    printf("  Suggested affinity: %d (%s)\n",
           ss.suggested_affinity,
           ss.suggested_affinity > 0 ? "trit" :
           ss.suggested_affinity < 0 ? "binary" : "any");
}

/* ---- Main Shell Loop -------------------------------------------------- */

/**
 * @brief Run the TBE interactive shell.
 *
 * Reads commands from stdin, dispatches to handlers.
 * Exit with "quit" command.
 */
static inline void tbe_run(tbe_state_t *tbe) {
    char line[256];
    char cmd[32];

    printf("\nseT5 TBE — Ternary Bootstrap Environment v0.1\n");
    printf("Type 'help' for commands.\n\n");

    while (tbe->running) {
        printf("tbe> ");
        if (!fgets(line, sizeof(line), stdin)) break;

        /* Strip newline */
        line[strcspn(line, "\n")] = '\0';
        if (line[0] == '\0') continue;

        /* Parse command */
        int n1 = 0, n2 = 0;
        char cv = 'U';

        if (sscanf(line, "%31s", cmd) != 1) continue;

        if (strcmp(cmd, "help") == 0) {
            tbe_cmd_help();
        } else if (strcmp(cmd, "quit") == 0 || strcmp(cmd, "exit") == 0) {
            tbe->running = 0;
        } else if (strcmp(cmd, "reg") == 0) {
            if (sscanf(line, "%*s %d", &n1) == 1)
                tbe_cmd_reg(tbe, n1);
            else
                printf("Usage: reg <n>\n");
        } else if (strcmp(cmd, "set") == 0) {
            if (sscanf(line, "%*s %d %d %c", &n1, &n2, &cv) == 3)
                tbe_cmd_set(tbe, n1, n2, cv);
            else
                printf("Usage: set <reg> <pos> <F|U|T>\n");
        } else if (strcmp(cmd, "dot") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2)
                tbe_cmd_dot(tbe, n1, n2);
            else
                printf("Usage: dot <a> <b>\n");
        } else if (strcmp(cmd, "fft") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2)
                tbe_cmd_fft(tbe, n1, n2);
            else
                printf("Usage: fft <reg> <offset>\n");
        } else if (strcmp(cmd, "conv") == 0) {
            if (sscanf(line, "%*s %d %d", &n1, &n2) == 2)
                tbe_cmd_conv(tbe, n1, n2);
            else
                printf("Usage: conv <reg> <int>\n");
        } else if (strcmp(cmd, "alloc") == 0) {
            if (sscanf(line, "%*s %d", &n1) == 1)
                tbe_cmd_alloc(tbe, n1);
            else
                printf("Usage: alloc <owner>\n");
        } else if (strcmp(cmd, "free") == 0) {
            if (sscanf(line, "%*s %d", &n1) == 1)
                tbe_cmd_free(tbe, n1);
            else
                printf("Usage: free <page>\n");
        } else if (strcmp(cmd, "cap") == 0) {
            tbe_cmd_cap(tbe);
        } else if (strcmp(cmd, "sched") == 0) {
            tbe_cmd_sched(tbe);
        } else if (strcmp(cmd, "noise") == 0) {
            char model[32] = "none";
            if (sscanf(line, "%*s %31s %d", model, &n1) == 2)
                tbe_cmd_noise(tbe, model, n1);
            else
                printf("Usage: noise <none|uni|gauss|mem|cosmic> <ppm>\n");
        } else if (strcmp(cmd, "wcet") == 0) {
            tbe_cmd_wcet(tbe);
        } else if (strcmp(cmd, "telem") == 0) {
            tbe_cmd_telem(tbe);
        } else {
            printf("Unknown command: %s (type 'help')\n", cmd);
        }
    }

    printf("TBE: Goodbye.\n");
}

#endif /* SET5_TBE_SHELL_H */
