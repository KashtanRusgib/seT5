/**
 * @file bench_unroll.c
 * @brief seT6 Benchmark — 4x Loop Unrolling Overhead Measurement
 *
 * Measures the overhead of 4x loop-unrolled bulk Kleene operations
 * vs. scalar loops. The Phase 3→4 gate requires < 5% overhead.
 *
 * Tests:
 *   1. Scalar AND loop vs. trit2_reg32_and_bulk (4x unrolled)
 *   2. Scalar OR loop vs. trit2_reg32_or_bulk
 *   3. DOT_TRIT dense vs. DOT_TRIT sparse (N:M pattern)
 *   4. RADIX_CONV throughput (conversions/sec)
 *
 * Build: gcc -O2 -Wall -Iinclude -Itools/compiler/include \
 *        -o bench_unroll tests/bench_unroll.c src/multiradix.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <time.h>
#include "set6/trit.h"
#include "set6/trit_emu.h"
#include "set6/trit_cast.h"
#include "set6/multiradix.h"

#define ITERS 1000000

static double elapsed_ms(struct timespec *start, struct timespec *end) {
    return (end->tv_sec - start->tv_sec) * 1000.0 +
           (end->tv_nsec - start->tv_nsec) / 1e6;
}

/* ---- Scalar reference loop (no unrolling) ----------------------------- */
__attribute__((noinline))
static void scalar_and_loop(trit2_reg32 *dst,
                            const trit2_reg32 *a,
                            const trit2_reg32 *b, int n) {
    for (int i = 0; i < n; i++) {
        dst[i].bits = a[i].bits & b[i].bits;
    }
}

__attribute__((noinline))
static void scalar_or_loop(trit2_reg32 *dst,
                           const trit2_reg32 *a,
                           const trit2_reg32 *b, int n) {
    for (int i = 0; i < n; i++) {
        dst[i].bits = a[i].bits | b[i].bits;
    }
}

/* Wrap bulk calls with noinline to prevent DCE at the call site */
__attribute__((noinline))
static void bulk_and_wrap(trit2_reg32 *dst,
                          const trit2_reg32 *a,
                          const trit2_reg32 *b, int n) {
    trit2_reg32_and_bulk(dst, a, b, n);
}

__attribute__((noinline))
static void bulk_or_wrap(trit2_reg32 *dst,
                         const trit2_reg32 *a,
                         const trit2_reg32 *b, int n) {
    trit2_reg32_or_bulk(dst, a, b, n);
}

int main(void) {
    printf("seT6 4x Unrolling Benchmark\n");
    printf("===========================\n");
    printf("Iterations: %d\n\n", ITERS);

    /* ---- Setup ---- */
    const int N = 64; /* 64 registers = 2048 trits */
    trit2_reg32 a[64], b[64], dst_scalar[64], dst_unrolled[64];

    for (int i = 0; i < N; i++) {
        a[i] = trit2_reg32_splat(TRIT2_TRUE);
        b[i] = trit2_reg32_splat(TRIT2_UNKNOWN);
    }

    struct timespec t0, t1;

    /* ---- Bench 1: Scalar AND ---- */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        scalar_and_loop(dst_scalar, a, b, N);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double scalar_and_ms = elapsed_ms(&t0, &t1);

    /* ---- Bench 2: 4x Unrolled AND ---- */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        bulk_and_wrap(dst_unrolled, a, b, N);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double unrolled_and_ms = elapsed_ms(&t0, &t1);

    double and_overhead = ((unrolled_and_ms - scalar_and_ms) / scalar_and_ms) * 100.0;

    printf("AND (64 regs x %dM iters):\n", ITERS / 1000000);
    printf("  Scalar:   %.2f ms\n", scalar_and_ms);
    printf("  4x Unroll:%.2f ms\n", unrolled_and_ms);
    printf("  Overhead: %.2f%% %s\n\n",
           and_overhead, (and_overhead < 5.0) ? "[PASS]" : "[WARN]");

    /* ---- Bench 3: Scalar OR ---- */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        scalar_or_loop(dst_scalar, a, b, N);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double scalar_or_ms = elapsed_ms(&t0, &t1);

    /* ---- Bench 4: 4x Unrolled OR ---- */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        bulk_or_wrap(dst_unrolled, a, b, N);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double unrolled_or_ms = elapsed_ms(&t0, &t1);

    double or_overhead = ((unrolled_or_ms - scalar_or_ms) / scalar_or_ms) * 100.0;

    printf("OR (64 regs x %dM iters):\n", ITERS / 1000000);
    printf("  Scalar:   %.2f ms\n", scalar_or_ms);
    printf("  4x Unroll:%.2f ms\n", unrolled_or_ms);
    printf("  Overhead: %.2f%% %s\n\n",
           or_overhead, (or_overhead < 5.0) ? "[PASS]" : "[WARN]");

    /* ---- Bench 5: DOT_TRIT dense vs sparse ---- */
    multiradix_state_t mr;
    multiradix_init(&mr);
    mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);

    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        dot_trit(&mr, 0, 1);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dot_dense_ms = elapsed_ms(&t0, &t1);

    /* Make reg 0 sparse (80% Unknown) */
    mr.regs[0] = trit2_reg32_splat(TRIT2_UNKNOWN);
    for (int i = 0; i < 6; i++)
        trit2_reg32_set(&mr.regs[0], i, TRIT2_TRUE);

    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        dot_trit(&mr, 0, 1);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double dot_sparse_ms = elapsed_ms(&t0, &t1);

    double sparse_speedup = ((dot_dense_ms - dot_sparse_ms) / dot_dense_ms) * 100.0;

    printf("DOT_TRIT (%dM iters):\n", ITERS / 1000000);
    printf("  Dense:    %.2f ms\n", dot_dense_ms);
    printf("  Sparse:   %.2f ms (80%% zero)\n", dot_sparse_ms);
    printf("  Speedup:  %.1f%% %s\n\n",
           sparse_speedup, sparse_speedup > 0 ? "[PASS]" : "[NEUTRAL]");

    /* ---- Bench 6: RADIX_CONV throughput ---- */
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int iter = 0; iter < ITERS; iter++) {
        radix_conv_to_ternary(&mr, 0, iter & 0x7FFF);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double conv_ms = elapsed_ms(&t0, &t1);
    double conv_per_sec = (ITERS / conv_ms) * 1000.0;

    printf("RADIX_CONV (%dM iters):\n", ITERS / 1000000);
    printf("  Time:     %.2f ms\n", conv_ms);
    printf("  Rate:     %.0f conv/sec\n\n", conv_per_sec);

    /* ---- Summary ---- */
    int pass = (and_overhead < 5.0) && (or_overhead < 5.0);
    printf("========================================\n");
    printf("Gate check: < 5%% overhead: %s\n", pass ? "PASS" : "FAIL");
    printf("========================================\n");

    return pass ? 0 : 1;
}
