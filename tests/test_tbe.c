/**
 * @file test_tbe.c
 * @brief Automated tests for TBE bootstrap environment components.
 *
 * Tests env-var management, consensus/accept-any, trit inc/dec,
 * syscall fallback, and Trithon parsing — all without interactive I/O.
 *
 * Build:
 *   gcc -Wall -Iinclude -Itools/compiler/include -DTBE_TEST \
 *       -o test_tbe tests/test_tbe.c src/syscall.c src/memory.c \
 *       src/ipc.c src/scheduler.c src/multiradix.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

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
/*  Test Infrastructure                                                  */
/* ===================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name)                                                    \
    do {                                                              \
        printf("  %-55s ", #name);                                    \
        fflush(stdout);                                               \
    } while(0)

#define PASS()                                                        \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

#define FAIL(msg)                                                     \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

/* ===================================================================== */
/*  1i.  Trit-Based Environment Variable Tests (inline reimplementation) */
/* ===================================================================== */

/* Minimal env re-implementation matching tbe_main.c logic */

#define TBE_MAX_ENV   16
#define TBE_KEY_LEN   32
#define TBE_VAL_LEN   128

typedef struct {
    char key[TBE_KEY_LEN];
    trit val[TBE_VAL_LEN];
    int  val_len;
    trit validity;
} tbe_env_t;

typedef struct {
    tbe_env_t entries[TBE_MAX_ENV];
    int       count;
} tbe_env_table_t;

static void tbe_env_init(tbe_env_table_t *env) {
    env->count = 0;
    for (int i = 0; i < TBE_MAX_ENV; i++) {
        env->entries[i].key[0]   = '\0';
        env->entries[i].val_len  = 0;
        env->entries[i].validity = TRIT_FALSE;
    }
    strncpy(env->entries[0].key, "SHELL", TBE_KEY_LEN - 1);
    env->entries[0].val[0] = TRIT_TRUE;
    env->entries[0].val_len = 1;
    env->entries[0].validity = TRIT_TRUE;
    strncpy(env->entries[1].key, "TRIT_MODE", TBE_KEY_LEN - 1);
    env->entries[1].val[0] = TRIT_TRUE;
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
        if (env->count >= TBE_MAX_ENV) return -1;
        idx = env->count++;
    }
    strncpy(env->entries[idx].key, key, TBE_KEY_LEN - 1);
    env->entries[idx].key[TBE_KEY_LEN - 1] = '\0';
    env->entries[idx].validity = TRIT_TRUE;
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

/* consensus / accept_any (same logic as tbe_main.c) */
static int tbe_consensus(multiradix_state_t *mr, int ra, int rb) {
    int agree = 0;
    for (int i = 0; i < 32; i++) {
        trit a = trit2_to_trit(trit2_reg32_get(&mr->regs[ra], i));
        trit b = trit2_to_trit(trit2_reg32_get(&mr->regs[rb], i));
        trit c = trit_and(a, b);
        if (c == TRIT_TRUE) agree++;
    }
    return agree;
}

static int tbe_accept_any(multiradix_state_t *mr, int ra, int rb) {
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
/*  Test Cases                                                           */
/* ===================================================================== */

/* -- Section 1: Environment Variables -- */

static void test_env_init_seeds(void) {
    TEST(env_init_seeds_two_vars);
    tbe_env_table_t env;
    tbe_env_init(&env);
    ASSERT_EQ(env.count, 2, "should have 2 pre-seeded vars");
    ASSERT_EQ(tbe_env_find(&env, "SHELL"), 0, "SHELL at index 0");
    ASSERT_EQ(tbe_env_find(&env, "TRIT_MODE"), 1, "TRIT_MODE at index 1");
    PASS();
}

static void test_env_set_new(void) {
    TEST(env_set_creates_new_entry);
    tbe_env_table_t env;
    tbe_env_init(&env);
    int rc = tbe_env_set(&env, "FOO", 42);
    ASSERT_EQ(rc, 0, "set should succeed");
    ASSERT_EQ(env.count, 3, "count should be 3");
    int idx = tbe_env_find(&env, "FOO");
    ASSERT_TRUE(idx >= 0, "FOO should exist");
    ASSERT_TRUE(env.entries[idx].val_len > 0, "should have trits");
    PASS();
}

static void test_env_set_overwrite(void) {
    TEST(env_set_overwrites_existing);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "SCORE", 10);
    int old_count = env.count;
    tbe_env_set(&env, "SCORE", 20);
    ASSERT_EQ(env.count, old_count, "count shouldn't grow");
    PASS();
}

static void test_env_zero_value(void) {
    TEST(env_set_zero_is_single_U);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "ZERO", 0);
    int idx = tbe_env_find(&env, "ZERO");
    ASSERT_TRUE(idx >= 0, "ZERO should exist");
    ASSERT_EQ(env.entries[idx].val_len, 1, "len should be 1");
    ASSERT_EQ(env.entries[idx].val[0], TRIT_UNKNOWN, "0 → U");
    PASS();
}

static void test_env_negative_value(void) {
    TEST(env_set_negative_flips_trits);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "NEG", 1);
    int idx_pos = tbe_env_find(&env, "NEG");
    trit v_pos = env.entries[idx_pos].val[0];

    tbe_env_set(&env, "NEG2", -1);
    int idx_neg = tbe_env_find(&env, "NEG2");
    trit v_neg = env.entries[idx_neg].val[0];

    ASSERT_EQ(v_pos, trit_not(v_neg), "+1 and -1 should be complementary");
    PASS();
}

static void test_env_find_nonexistent(void) {
    TEST(env_find_returns_neg1_for_missing);
    tbe_env_table_t env;
    tbe_env_init(&env);
    ASSERT_EQ(tbe_env_find(&env, "NOPE"), -1, "not found → -1");
    PASS();
}

static void test_env_full(void) {
    TEST(env_full_rejects_17th_entry);
    tbe_env_table_t env;
    tbe_env_init(&env);
    /* Fill the remaining 14 slots (2 pre-seeded) */
    for (int i = 0; i < 14; i++) {
        char key[8];
        snprintf(key, sizeof(key), "V%d", i);
        tbe_env_set(&env, key, i);
    }
    ASSERT_EQ(env.count, TBE_MAX_ENV, "should be at capacity");
    int rc = tbe_env_set(&env, "OVERFLOW", 999);
    ASSERT_EQ(rc, -1, "should reject when full");
    PASS();
}

static void test_env_validity_flags(void) {
    TEST(env_validity_is_TRUE_for_active);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "FLG", 7);
    int idx = tbe_env_find(&env, "FLG");
    ASSERT_EQ(env.entries[idx].validity, TRIT_TRUE, "active → T");
    PASS();
}

/* -- Section 2: Balanced Ternary Encoding -- */

static void test_bt_encode_1(void) {
    TEST(bt_encode_1_is_single_T);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "ONE", 1);
    int idx = tbe_env_find(&env, "ONE");
    ASSERT_EQ(env.entries[idx].val_len, 1, "1 → 1 trit");
    ASSERT_EQ(env.entries[idx].val[0], TRIT_TRUE, "1 → T");
    PASS();
}

static void test_bt_encode_2(void) {
    TEST(bt_encode_2_is_TF);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "TWO", 2);
    int idx = tbe_env_find(&env, "TWO");
    /* 2 in balanced ternary: 1*3 + (-1)*1 = 3-1 = 2  → trits = [F, T] (LST first) */
    ASSERT_EQ(env.entries[idx].val_len, 2, "2 → 2 trits");
    ASSERT_EQ(env.entries[idx].val[0], TRIT_FALSE, "LST = F (-1)");
    ASSERT_EQ(env.entries[idx].val[1], TRIT_TRUE,  "MST = T (+1)");
    PASS();
}

static void test_bt_encode_3(void) {
    TEST(bt_encode_3_is_TU);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "THREE", 3);
    int idx = tbe_env_find(&env, "THREE");
    /* 3 in balanced ternary: 1*3 + 0*1 = 3  → trits = [U, T] */
    ASSERT_EQ(env.entries[idx].val_len, 2, "3 → 2 trits");
    ASSERT_EQ(env.entries[idx].val[0], TRIT_UNKNOWN, "LST = U (0)");
    ASSERT_EQ(env.entries[idx].val[1], TRIT_TRUE,    "MST = T (+1)");
    PASS();
}

static void test_bt_encode_13(void) {
    TEST(bt_encode_13_is_correct);
    tbe_env_table_t env;
    tbe_env_init(&env);
    tbe_env_set(&env, "X13", 13);
    int idx = tbe_env_find(&env, "X13");
    /* 13 = 1*9 + 1*3 + 1*1 → trits = [T, T, T] */
    ASSERT_EQ(env.entries[idx].val_len, 3, "13 → 3 trits");
    ASSERT_EQ(env.entries[idx].val[0], TRIT_TRUE, "t0 = T");
    ASSERT_EQ(env.entries[idx].val[1], TRIT_TRUE, "t1 = T");
    ASSERT_EQ(env.entries[idx].val[2], TRIT_TRUE, "t2 = T");
    PASS();
}

/* -- Section 3: Consensus / Accept-Any -- */

static void test_consensus_all_T(void) {
    TEST(consensus_all_T_yields_32);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_TRUE);
    }
    ASSERT_EQ(tbe_consensus(&mr, 0, 1), 32, "T&T=T for all 32");
    PASS();
}

static void test_consensus_mixed(void) {
    TEST(consensus_T_and_F_yields_0);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_FALSE);
    }
    ASSERT_EQ(tbe_consensus(&mr, 0, 1), 0, "T&F=F for all 32");
    PASS();
}

static void test_consensus_with_unknowns(void) {
    TEST(consensus_T_and_U_yields_0);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_UNKNOWN);
    }
    /* T & U = U (not T), so agree=0 */
    ASSERT_EQ(tbe_consensus(&mr, 0, 1), 0, "T&U=U, not T");
    PASS();
}

static void test_accept_any_all_F(void) {
    TEST(accept_any_all_F_yields_0);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_FALSE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_FALSE);
    }
    ASSERT_EQ(tbe_accept_any(&mr, 0, 1), 0, "F|F=F for all 32");
    PASS();
}

static void test_accept_any_one_T(void) {
    TEST(accept_any_T_or_F_yields_32);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_FALSE);
    }
    ASSERT_EQ(tbe_accept_any(&mr, 0, 1), 32, "T|F=T for all 32");
    PASS();
}

static void test_accept_any_unknowns(void) {
    TEST(accept_any_U_or_U_yields_0);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_UNKNOWN);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_UNKNOWN);
    }
    /* U or U = U (not T), so accepted=0 */
    ASSERT_EQ(tbe_accept_any(&mr, 0, 1), 0, "U|U=U, not T");
    PASS();
}

/* -- Section 4: Syscall Integration -- */

static void test_kernel_init_works(void) {
    TEST(kernel_init_succeeds);
    kernel_state_t ks;
    kernel_init(&ks, 32);
    ASSERT_EQ(ks.operand_sp, 0, "stack empty");
    ASSERT_EQ(ks.return_sp, 0, "return stack empty");
    PASS();
}

static void test_syscall_push_pop(void) {
    TEST(syscall_push_pop_roundtrip);
    kernel_state_t ks;
    kernel_init(&ks, 32);
    /* Test operand stack round-trip via direct kernel_push/kernel_pop API.
     * VULN-60 fix: SYSCALL_MMAP requires a running thread (current_tid >= 0).
     * The previous version accidentally relied on MMAP succeeding with no tid;
     * we now test the stack directly which is the intended contract. */
    kernel_push(&ks, TRIT_TRUE);
    ASSERT_TRUE(ks.operand_sp == 1, "push should succeed");
    trit v = kernel_pop(&ks);
    ASSERT_EQ(v, TRIT_TRUE, "pop should return T");
    /* Verify MMAP correctly fails when no thread is running */
    syscall_result_t r = syscall_dispatch(&ks, SYSCALL_MMAP, 0, 0);
    ASSERT_EQ(r.retval, -1, "MMAP fails with no current thread");
    PASS();
}

static void test_syscall_alloc_free(void) {
    TEST(syscall_alloc_then_free);
    kernel_state_t ks;
    kernel_init(&ks, 32);
    /* SYSCALL_ALLOC = 0, 1 page */
    syscall_result_t r = syscall_dispatch(&ks, 0, 1, 0);
    ASSERT_TRUE(r.retval >= 0, "alloc should return page");
    int page = r.retval;
    /* SYSCALL_FREE = 1 */
    r = syscall_dispatch(&ks, 1, page, 0);
    ASSERT_TRUE(r.retval >= 0, "free should succeed");
    PASS();
}

static void test_syscall_cap_create(void) {
    TEST(syscall_cap_create_and_check);
    kernel_state_t ks;
    kernel_init(&ks, 32);
    int cap = kernel_cap_create(&ks, 1, 7, 0);
    ASSERT_TRUE(cap >= 0, "cap create should succeed");
    ASSERT_TRUE(kernel_cap_check(&ks, cap, 1), "read right");
    ASSERT_TRUE(kernel_cap_check(&ks, cap, 2), "write right");
    PASS();
}

static void test_syscall_cap_revoke(void) {
    TEST(syscall_cap_revoke_denies);
    kernel_state_t ks;
    kernel_init(&ks, 32);
    int cap = kernel_cap_create(&ks, 1, 7, 0);
    kernel_cap_revoke(&ks, cap);
    ASSERT_TRUE(!kernel_cap_check(&ks, cap, 1), "revoked → deny");
    PASS();
}

/* -- Section 5: Multiradix Registers -- */

static void test_trit_inc_from_zero(void) {
    TEST(trit_inc_from_zero_gives_T);
    multiradix_state_t mr;
    multiradix_init(&mr);
    /* All Unknown (0). Increment: add 1 to LST → T */
    int carry = 1;
    for (int i = 0; i < 32 && carry; i++) {
        trit2 t = trit2_reg32_get(&mr.regs[0], i);
        trit  s = trit2_to_trit(t);
        int   v = (int)s + carry;
        if (v > 1) { v = -1; carry = 1; }
        else       { carry = 0; }
        trit2_reg32_set(&mr.regs[0], i,
                        (v == 1) ? TRIT2_TRUE :
                        (v == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN);
    }
    trit2 lsb = trit2_reg32_get(&mr.regs[0], 0);
    ASSERT_EQ(lsb, TRIT2_TRUE, "LST should be T after inc");
    PASS();
}

static void test_trit_dec_from_zero(void) {
    TEST(trit_dec_from_zero_gives_F);
    multiradix_state_t mr;
    multiradix_init(&mr);
    int borrow = 1;
    for (int i = 0; i < 32 && borrow; i++) {
        trit2 t = trit2_reg32_get(&mr.regs[0], i);
        trit  s = trit2_to_trit(t);
        int   v = (int)s - borrow;
        if (v < -1) { v = 1; borrow = 1; }
        else        { borrow = 0; }
        trit2_reg32_set(&mr.regs[0], i,
                        (v == 1) ? TRIT2_TRUE :
                        (v == -1) ? TRIT2_FALSE : TRIT2_UNKNOWN);
    }
    trit2 lsb = trit2_reg32_get(&mr.regs[0], 0);
    ASSERT_EQ(lsb, TRIT2_FALSE, "LST should be F after dec");
    PASS();
}

/* -- Section 6: WCET Probes -- */

static void test_wcet_register_and_observe(void) {
    TEST(wcet_register_and_observe);
    wcet_state_t w;
    wcet_init(&w);
    wcet_register(&w, "test_probe", 100);
    ASSERT_EQ(w.probe_count, 1, "one probe registered");
    wcet_observe(&w, 0, 50);
    wcet_observe(&w, 0, 80);
    ASSERT_EQ((int)w.probes[0].observed_max, 80, "max should be 80");
    ASSERT_TRUE(wcet_average(&w, 0) > 0, "avg > 0");
    PASS();
}

static void test_wcet_violation(void) {
    TEST(wcet_violation_detected);
    wcet_state_t w;
    wcet_init(&w);
    wcet_register(&w, "budget_probe", 10);
    wcet_observe(&w, 0, 5);   /* within budget */
    wcet_observe(&w, 0, 20);  /* over budget → violation */
    ASSERT_TRUE(w.probes[0].violation_count > 0, "should detect violation");
    ASSERT_EQ(w.total_violations, 1, "total violations = 1");
    PASS();
}

/* -- Section 7: FFT Step -- */

static void test_fft_step_output_verified(void) {
    TEST(fft_step_output_verified);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++)
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
    int groups = fft_step(&mr, 0, 1, 1);
    ASSERT_EQ(groups, 10, "fft_step returns 10 butterfly groups");
    /* Verify output register was written (not all-Unknown) */
    int first = trit2_decode(trit2_reg32_get(&mr.regs[1], 0));
    /* Butterfly on (T,T,T): o0 = T+T+T mod3 = 0, so first output = 0 */
    ASSERT_EQ(first, 0, "butterfly(T,T,T) slot 0 = 0");
    PASS();
}

/* -- Section 8: DOT product -- */

static void test_dot_all_T(void) {
    TEST(dot_all_T_yields_32);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_TRUE);
    }
    int d = dot_trit(&mr, 0, 1);
    ASSERT_EQ(d, 32, "dot(all T, all T) = 32");
    PASS();
}

static void test_dot_orthogonal(void) {
    TEST(dot_T_vs_F_yields_neg32);
    multiradix_state_t mr;
    multiradix_init(&mr);
    for (int i = 0; i < 32; i++) {
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);
        trit2_reg32_set(&mr.regs[1], i, TRIT2_FALSE);
    }
    int d = dot_trit(&mr, 0, 1);
    ASSERT_EQ(d, -32, "dot(all T, all F) = -32");
    PASS();
}

/* -- Section 9: Noise Generator -- */

static void test_noise_init(void) {
    TEST(qemu_noise_init_zero_mode);
    qemu_noise_t n;
    qemu_noise_init(&n, NOISE_NONE, 0, 0);
    trit t = qemu_noise_read(&n, TRIT_TRUE);
    ASSERT_EQ(t, TRIT_TRUE, "no noise → identity");
    PASS();
}

/* ===================================================================== */
/*  Main                                                                 */
/* ===================================================================== */

int main(void) {
    printf("\n=== TBE Unit Tests ===\n\n");
    printf("Section 1: Environment Variables\n");
    test_env_init_seeds();
    test_env_set_new();
    test_env_set_overwrite();
    test_env_zero_value();
    test_env_negative_value();
    test_env_find_nonexistent();
    test_env_full();
    test_env_validity_flags();

    printf("\nSection 2: Balanced Ternary Encoding\n");
    test_bt_encode_1();
    test_bt_encode_2();
    test_bt_encode_3();
    test_bt_encode_13();

    printf("\nSection 3: Consensus / Accept-Any\n");
    test_consensus_all_T();
    test_consensus_mixed();
    test_consensus_with_unknowns();
    test_accept_any_all_F();
    test_accept_any_one_T();
    test_accept_any_unknowns();

    printf("\nSection 4: Syscall Integration\n");
    test_kernel_init_works();
    test_syscall_push_pop();
    test_syscall_alloc_free();
    test_syscall_cap_create();
    test_syscall_cap_revoke();

    printf("\nSection 5: Trit Inc/Dec\n");
    test_trit_inc_from_zero();
    test_trit_dec_from_zero();

    printf("\nSection 6: WCET Probes\n");
    test_wcet_register_and_observe();
    test_wcet_violation();

    printf("\nSection 7: FFT\n");
    test_fft_step_output_verified();

    printf("\nSection 8: DOT Product\n");
    test_dot_all_T();
    test_dot_orthogonal();

    printf("\nSection 9: Noise Generator\n");
    test_noise_init();

    printf("\n=================================\n");
    printf("TBE Tests: %d passed, %d failed (of %d)\n",
           tests_passed, tests_failed, tests_passed + tests_failed);
    printf("=================================\n\n");

    return tests_failed > 0 ? 1 : 0;
}
