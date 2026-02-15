/**
 * @file trit_emu_bench.c
 * @brief seT6 Phase 1.2 — Ternary Emulation Benchmark
 *
 * Correctness validation and performance benchmarking for 2-bit ternary
 * emulation on binary hardware. Uses 4x-unrolled bulk ops.
 *
 * Build: gcc -std=c99 -D_POSIX_C_SOURCE=200809L -O2 -Iinclude \
 *            -o demo/trit_emu_bench demo/trit_emu_bench.c
 *
 * Targets: 1M AND ops < 0.002s;  <15% overhead vs binary AND baseline.
 *
 * References: Setun (Brusentsov 1958), AFP "Three-Valued Logic",
 *             seT6 INITIAL_PROJECT_ANSWERS
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#define _POSIX_C_SOURCE 200809L

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <string.h>
#include "set6/trit.h"
#include "set6/trit_emu.h"

/* ---------- helpers ---------------------------------------------------- */

/** @brief High-resolution monotonic clock in seconds. */
static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/** @brief Volatile sink to prevent dead-code elimination. */
static volatile uint64_t sink;

/* ---------- correctness checks ----------------------------------------- */

/**
 * @brief Validate scalar trit2 ops against Kleene truth tables.
 * @return 1 if all tests pass, 0 on failure.
 */
static int test_scalar_ops(void) {
    static const trit2 vals[3] = { TRIT2_FALSE, TRIT2_UNKNOWN, TRIT2_TRUE };
    int pass = 1;

    /* Full 3x3 AND truth table: AND = min */
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

    /* Full 3x3 OR truth table: OR = max */
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            trit2 got = trit2_or(vals[i], vals[j]);
            trit2 direct = (vals[i] > vals[j]) ? vals[i] : vals[j];
            if (got != direct) {
                fprintf(stderr, "FAIL: trit2_or(%u,%u) = %u, expected %u\n",
                        vals[i], vals[j], got, direct);
                pass = 0;
            }
        }

    /* NOT involution: NOT(NOT(x)) == x */
    for (int i = 0; i < 3; i++) {
        trit2 nn = trit2_not(trit2_not(vals[i]));
        if (nn != vals[i]) {
            fprintf(stderr, "FAIL: NOT(NOT(%u)) = %u\n", vals[i], nn);
            pass = 0;
        }
    }

    /* De Morgan: NOT(AND(a,b)) == OR(NOT(a), NOT(b)) */
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            trit2 lhs = trit2_not(trit2_and(vals[i], vals[j]));
            trit2 rhs = trit2_or(trit2_not(vals[i]), trit2_not(vals[j]));
            if (lhs != rhs) {
                fprintf(stderr, "FAIL: De Morgan AND(%u,%u): %u != %u\n",
                        vals[i], vals[j], lhs, rhs);
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

    /* Encode/decode round-trip */
    int test_vals[] = { -1, 0, 1 };
    for (int i = 0; i < 3; i++) {
        trit2 enc = trit2_encode(test_vals[i]);
        int dec = trit2_decode(enc);
        if (dec != test_vals[i]) {
            fprintf(stderr, "FAIL: encode(%d)->decode = %d\n",
                    test_vals[i], dec);
            pass = 0;
        }
    }

    return pass;
}

/**
 * @brief Validate 32-trit register (SIMD) operations.
 * @return 1 if all tests pass, 0 on failure.
 */
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

    /* All-false OR all-true = all-true */
    result = trit2_reg32_or(all_f, all_t);
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&result, i) != TRIT2_TRUE) {
            fprintf(stderr, "FAIL: reg32 F OR T at [%d] != T\n", i);
            pass = 0;
        }
    }

    /* NOT(NOT(x)) == x for mixed pattern */
    static const trit2 tval[3] = { TRIT2_FALSE, TRIT2_UNKNOWN, TRIT2_TRUE };
    trit2_reg32 mixed;
    mixed.bits = 0;
    for (int i = 0; i < 32; i++)
        trit2_reg32_set(&mixed, i, tval[i % 3]);
    trit2_reg32 nn = trit2_reg32_not(trit2_reg32_not(mixed));
    if (nn.bits != mixed.bits) {
        fprintf(stderr, "FAIL: reg32 NOT(NOT(mixed)) != mixed\n");
        pass = 0;
    }

    /* De Morgan on registers */
    trit2_reg32 dm_lhs = trit2_reg32_not(trit2_reg32_and(mixed, all_u));
    trit2_reg32 dm_rhs = trit2_reg32_or(trit2_reg32_not(mixed),
                                         trit2_reg32_not(all_u));
    if (dm_lhs.bits != dm_rhs.bits) {
        fprintf(stderr, "FAIL: reg32 De Morgan AND violated\n");
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

    /* Census check */
    int nf, nu, nt, nx;
    trit2_reg32_census(mixed, &nf, &nu, &nt, &nx);
    if (nf != 11 || nu != 11 || nt != 10 || nx != 0) {
        fprintf(stderr, "FAIL: census F=%d U=%d T=%d X=%d (expected 11,11,10,0)\n",
                nf, nu, nt, nx);
        pass = 0;
    }

    return pass;
}

/**
 * @brief Test the bulk (4x unrolled) AND operation.
 * @return 1 if pass, 0 on failure.
 */
static int test_bulk_ops(void) {
    int pass = 1;
    const int N = 17;  /* odd to test remainder handling */
    trit2_reg32 a[17], b[17], c[17], ref[17];

    static const trit2 tval[3] = { TRIT2_FALSE, TRIT2_UNKNOWN, TRIT2_TRUE };
    for (int i = 0; i < N; i++) {
        a[i] = trit2_reg32_splat(tval[i % 3]);
        b[i] = trit2_reg32_splat(tval[(i + 1) % 3]);
        ref[i] = trit2_reg32_and(a[i], b[i]);
    }

    trit2_reg32_and_bulk(c, a, b, N);

    for (int i = 0; i < N; i++) {
        if (c[i].bits != ref[i].bits) {
            fprintf(stderr, "FAIL: bulk_and[%d] = 0x%llx, expected 0x%llx\n",
                    i, (unsigned long long)c[i].bits,
                    (unsigned long long)ref[i].bits);
            pass = 0;
        }
    }

    return pass;
}

/* ---------- benchmarks ------------------------------------------------- */

#define N_OPS      1000000   /**< 1M logical operations */
#define N_REGS     (N_OPS / 32)  /**< 32 ops per register */
#define N_WARMUP   5
#define N_TRIALS   10        /**< Best-of for stable measurement */

/**
 * @brief Benchmark 1M Kleene AND operations using bulk SIMD (4x unrolled).
 * @return Best elapsed time in seconds.
 */
static double bench_trit_and(void) {
    trit2_reg32 *a = (trit2_reg32 *)malloc(N_REGS * sizeof(trit2_reg32));
    trit2_reg32 *b = (trit2_reg32 *)malloc(N_REGS * sizeof(trit2_reg32));
    trit2_reg32 *c = (trit2_reg32 *)malloc(N_REGS * sizeof(trit2_reg32));
    if (!a || !b || !c) { fprintf(stderr, "OOM\n"); exit(1); }

    srand(42);
    for (int i = 0; i < N_REGS; i++) {
        a[i].bits = ((uint64_t)(unsigned)rand() << 32) | (unsigned)rand();
        b[i].bits = ((uint64_t)(unsigned)rand() << 32) | (unsigned)rand();
        /* Clear fault pairs (10) — flip to unknown (01) */
        uint64_t af = (a[i].bits >> 1) & ~a[i].bits & TRIT2_LO_MASK;
        a[i].bits ^= (af | (af << 1));
        uint64_t bf = (b[i].bits >> 1) & ~b[i].bits & TRIT2_LO_MASK;
        b[i].bits ^= (bf | (bf << 1));
    }

    /* Warmup */
    for (int w = 0; w < N_WARMUP; w++)
        trit2_reg32_and_bulk(c, a, b, N_REGS);

    /* Timed trials — best-of */
    double best = 1e9;
    for (int trial = 0; trial < N_TRIALS; trial++) {
        double t0 = now_sec();
        trit2_reg32_and_bulk(c, a, b, N_REGS);
        double t1 = now_sec();
        double elapsed = t1 - t0;
        if (elapsed < best) best = elapsed;
    }

    /* Prevent DCE */
    uint64_t s = 0;
    for (int i = 0; i < N_REGS; i++) s ^= c[i].bits;
    sink = s;

    free(a); free(b); free(c);
    return best;
}

/**
 * @brief Benchmark 1M binary AND operations (baseline, 4x unrolled for fairness).
 * @return Best elapsed time in seconds.
 */
static double bench_binary_and(void) {
    uint64_t *a = (uint64_t *)malloc(N_REGS * sizeof(uint64_t));
    uint64_t *b = (uint64_t *)malloc(N_REGS * sizeof(uint64_t));
    uint64_t *c = (uint64_t *)malloc(N_REGS * sizeof(uint64_t));
    if (!a || !b || !c) { fprintf(stderr, "OOM\n"); exit(1); }

    srand(42);
    for (int i = 0; i < N_REGS; i++) {
        a[i] = ((uint64_t)(unsigned)rand() << 32) | (unsigned)rand();
        b[i] = ((uint64_t)(unsigned)rand() << 32) | (unsigned)rand();
    }

    /* Warmup (4x unrolled to match trit benchmark) */
    for (int w = 0; w < N_WARMUP; w++) {
        int j = 0;
        for (; j + 3 < N_REGS; j += 4) {
            c[j+0] = a[j+0] & b[j+0];
            c[j+1] = a[j+1] & b[j+1];
            c[j+2] = a[j+2] & b[j+2];
            c[j+3] = a[j+3] & b[j+3];
        }
        for (; j < N_REGS; j++)
            c[j] = a[j] & b[j];
    }

    /* Timed trials */
    double best = 1e9;
    for (int trial = 0; trial < N_TRIALS; trial++) {
        double t0 = now_sec();
        int j = 0;
        for (; j + 3 < N_REGS; j += 4) {
            c[j+0] = a[j+0] & b[j+0];
            c[j+1] = a[j+1] & b[j+1];
            c[j+2] = a[j+2] & b[j+2];
            c[j+3] = a[j+3] & b[j+3];
        }
        for (; j < N_REGS; j++)
            c[j] = a[j] & b[j];
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
    printf("=== seT6 Ternary Emulation Benchmark ===\n\n");

    /* Correctness */
    printf("--- Correctness Tests ---\n");
    int p1 = test_scalar_ops();
    printf("  Scalar ops:     %s\n", p1 ? "PASS" : "FAIL");
    int p2 = test_reg32_ops();
    printf("  Reg32 ops:      %s\n", p2 ? "PASS" : "FAIL");
    int p3 = test_bulk_ops();
    printf("  Bulk (4x unr):  %s\n", p3 ? "PASS" : "FAIL");

    if (!p1 || !p2 || !p3) {
        fprintf(stderr, "\nCorrectness FAILED — aborting benchmark.\n");
        return 1;
    }

    /* Benchmark */
    printf("\n--- Benchmark: 1M Kleene AND (32 trits/op, %d reg ops) ---\n", N_REGS);
    printf("    Warmup: %d iters, Trials: %d (best-of)\n\n", N_WARMUP, N_TRIALS);

    double t_trit = bench_trit_and();
    double t_bin  = bench_binary_and();
    double overhead = (t_trit - t_bin) / t_bin * 100.0;

    printf("  Ternary AND:  %.6f s  (%.1f Mops/s)\n",
           t_trit, (double)N_OPS / t_trit / 1e6);
    printf("  Binary  AND:  %.6f s  (%.1f Mops/s)\n",
           t_bin, (double)N_OPS / t_bin / 1e6);
    printf("  Overhead:     %.1f%%\n", overhead);

    /* Gate checks */
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
