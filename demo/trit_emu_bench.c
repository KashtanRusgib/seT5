/*
 * seT5 Phase 1.2 — Ternary Emulation Benchmark
 * Build: gcc -std=c99 -O2 -Iinclude -o demo/trit_emu_bench demo/trit_emu_bench.c
 *
 * Targets: 1M AND ops < 0.002s;  <15% overhead vs binary AND baseline.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include "set5/trit.h"
#include "set5/trit_emu.h"

/* ---------- helpers ---------------------------------------------------- */

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static volatile uint64_t sink;

/* ---------- correctness checks ----------------------------------------- */

static int test_scalar_ops(void) {
    static const trit2 vals[3] = { TRIT2_FALSE, TRIT2_UNKNOWN, TRIT2_TRUE };
    int pass = 1;

    /* Verify Kleene AND = min */
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            trit2 got = trit2_and(vals[i], vals[j]);
            trit2 direct = (vals[i] < vals[j]) ? vals[i] : vals[j];
            if (got != direct) {
                fprintf(stderr, "FAIL: trit2_and(%u,%u) = %u, expected %u\n",
                        vals[i], vals[j], got, direct);
                pass = 0;
            }
        }

    /* NOT involution */
    for (int i = 0; i < 3; i++) {
        trit2 nn = trit2_not(trit2_not(vals[i]));
        if (nn != vals[i]) {
            fprintf(stderr, "FAIL: NOT(NOT(%u)) = %u\n", vals[i], nn);
            pass = 0;
        }
    }

    /* Fault detection */
    if (!trit2_is_fault(TRIT2_FAULT)) {
        fprintf(stderr, "FAIL: TRIT2_FAULT not detected\n");
        pass = 0;
    }
    if (trit2_is_fault(TRIT2_TRUE)) {
        fprintf(stderr, "FAIL: TRIT2_TRUE detected as fault\n");
        pass = 0;
    }

    return pass;
}

static int test_reg32_ops(void) {
    int pass = 1;

    /* All-true AND all-unknown = all-unknown */
    trit2_reg32 all_t = trit2_reg32_splat(TRIT2_TRUE);
    trit2_reg32 all_u = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32 result = trit2_reg32_and(all_t, all_u);
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&result, i) != TRIT2_UNKNOWN) {
            fprintf(stderr, "FAIL: reg32 T AND U at [%d] != U\n", i);
            pass = 0;
        }
    }

    /* All-false AND anything = all-false */
    trit2_reg32 all_f = trit2_reg32_splat(TRIT2_FALSE);
    result = trit2_reg32_and(all_f, all_t);
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&result, i) != TRIT2_FALSE) {
            fprintf(stderr, "FAIL: reg32 F AND T at [%d] != F\n", i);
            pass = 0;
        }
    }

    /* NOT(NOT(x)) == x */
    trit2_reg32 mixed;
    mixed.bits = 0;
    for (int i = 0; i < 32; i++)
        trit2_reg32_set(&mixed, i, (trit2)(i % 3));
    trit2_reg32 nn = trit2_reg32_not(trit2_reg32_not(mixed));
    if (nn.bits != mixed.bits) {
        fprintf(stderr, "FAIL: reg32 NOT(NOT(mixed)) != mixed\n");
        pass = 0;
    }

    /* Fault detection */
    trit2_reg32 clean = trit2_reg32_splat(TRIT2_TRUE);
    if (trit2_reg32_has_fault(clean)) {
        fprintf(stderr, "FAIL: clean reg32 has fault\n");
        pass = 0;
    }
    trit2_reg32 dirty = clean;
    trit2_reg32_set(&dirty, 15, TRIT2_FAULT);
    if (!trit2_reg32_has_fault(dirty)) {
        fprintf(stderr, "FAIL: dirty reg32 fault not detected\n");
        pass = 0;
    }

    return pass;
}

/* ---------- benchmarks ------------------------------------------------- */

#define N_OPS      1000000
#define N_REGS     (N_OPS / 32)
#define N_WARMUP   3
#define N_TRIALS   5

static double bench_trit_and(void) {
    trit2_reg32 *a = (trit2_reg32 *)malloc(N_REGS * sizeof(trit2_reg32));
    trit2_reg32 *b = (trit2_reg32 *)malloc(N_REGS * sizeof(trit2_reg32));
    trit2_reg32 *c = (trit2_reg32 *)malloc(N_REGS * sizeof(trit2_reg32));
    if (!a || !b || !c) { fprintf(stderr, "OOM\n"); exit(1); }

    srand(42);
    for (int i = 0; i < N_REGS; i++) {
        a[i].bits = ((uint64_t)rand() << 32) | (uint64_t)rand();
        b[i].bits = ((uint64_t)rand() << 32) | (uint64_t)rand();
        /* Clear fault bits */
        a[i].bits &= ~(a[i].bits & TRIT2_HI_MASK & ((a[i].bits & TRIT2_LO_MASK) << 1));
        b[i].bits &= ~(b[i].bits & TRIT2_HI_MASK & ((b[i].bits & TRIT2_LO_MASK) << 1));
    }

    for (int w = 0; w < N_WARMUP; w++)
        for (int i = 0; i < N_REGS; i++)
            c[i] = trit2_reg32_and(a[i], b[i]);

    double best = 1e9;
    for (int trial = 0; trial < N_TRIALS; trial++) {
        double t0 = now_sec();
        for (int i = 0; i < N_REGS; i++)
            c[i] = trit2_reg32_and(a[i], b[i]);
        double t1 = now_sec();
        double elapsed = t1 - t0;
        if (elapsed < best) best = elapsed;
    }

    uint64_t s = 0;
    for (int i = 0; i < N_REGS; i++) s ^= c[i].bits;
    sink = s;

    free(a); free(b); free(c);
    return best;
}

static double bench_binary_and(void) {
    uint64_t *a = (uint64_t *)malloc(N_REGS * sizeof(uint64_t));
    uint64_t *b = (uint64_t *)malloc(N_REGS * sizeof(uint64_t));
    uint64_t *c = (uint64_t *)malloc(N_REGS * sizeof(uint64_t));
    if (!a || !b || !c) { fprintf(stderr, "OOM\n"); exit(1); }

    srand(42);
    for (int i = 0; i < N_REGS; i++) {
        a[i] = ((uint64_t)rand() << 32) | (uint64_t)rand();
        b[i] = ((uint64_t)rand() << 32) | (uint64_t)rand();
    }

    for (int w = 0; w < N_WARMUP; w++)
        for (int i = 0; i < N_REGS; i++)
            c[i] = a[i] & b[i];

    double best = 1e9;
    for (int trial = 0; trial < N_TRIALS; trial++) {
        double t0 = now_sec();
        for (int i = 0; i < N_REGS; i++)
            c[i] = a[i] & b[i];
        double t1 = now_sec();
        double elapsed = t1 - t0;
        if (elapsed < best) best = elapsed;
    }

    uint64_t s = 0;
    for (int i = 0; i < N_REGS; i++) s ^= c[i];
    sink = s;

    free(a); free(b); free(c);
    return best;
}

/* ---------- main ------------------------------------------------------- */

int main(void) {
    printf("=== seT5 Ternary Emulation Benchmark ===\n\n");

    printf("--- Correctness Tests ---\n");
    int p1 = test_scalar_ops();
    printf("  Scalar ops:  %s\n", p1 ? "PASS" : "FAIL");
    int p2 = test_reg32_ops();
    printf("  Reg32 ops:   %s\n", p2 ? "PASS" : "FAIL");

    if (!p1 || !p2) {
        fprintf(stderr, "\nCorrectness FAILED — aborting benchmark.\n");
        return 1;
    }

    printf("\n--- Benchmark: 1M Kleene AND (32 trits/op, %d reg ops) ---\n", N_REGS);

    double t_trit = bench_trit_and();
    double t_bin  = bench_binary_and();
    double overhead = (t_trit - t_bin) / t_bin * 100.0;

    printf("  Ternary AND:  %.6f s  (%.1f Mops/s)\n",
           t_trit, (double)N_OPS / t_trit / 1e6);
    printf("  Binary  AND:  %.6f s  (%.1f Mops/s)\n",
           t_bin, (double)N_OPS / t_bin / 1e6);
    printf("  Overhead:     %.1f%%\n", overhead);

    int time_ok = (t_trit < 0.002);
    int overhead_ok = (overhead < 15.0);

    printf("\n--- Gate Checks ---\n");
    printf("  Time < 0.002s:     %s (%.6f s)\n",
           time_ok ? "PASS" : "FAIL", t_trit);
    printf("  Overhead < 15%%:    %s (%.1f%%)\n",
           overhead_ok ? "PASS" : "FAIL", overhead);

    printf("\n=== %s ===\n",
           (time_ok && overhead_ok) ? "ALL GATES PASSED" : "GATES FAILED");

    return (time_ok && overhead_ok) ? 0 : 1;
}
