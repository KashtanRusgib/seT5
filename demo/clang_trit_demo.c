/**
 * @file clang_trit_demo.c
 * @brief seT5 End-to-End Clang Trit Demo
 *
 * Demonstrates balanced ternary operations using the seT5 __trit type
 * extension. This file compiles cleanly under both:
 *   - Standard GCC/Clang (via the compatibility shim)
 *   - seT5-Clang with native __trit support (future)
 *
 * Usage:
 *   gcc -Wall -Iinclude -o clang_trit_demo demo/clang_trit_demo.c
 *   ./clang_trit_demo
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include "set5/trit.h"
#include "set5/trit_type.h"
#include "set5/trit_emu.h"
#include "set5/trit_cast.h"
#include "set5/multiradix.h"

/*
 * When compiled with seT5-Clang (future), the __trit keyword is native.
 * Under stock compilers, we use the trit_checked() shim from trit_type.h.
 *
 *   #pragma clang trit_mode(kleene)
 *
 * This demo works with both paths.
 */

/* ---- Kleene K₃ Logic Demo -------------------------------------------- */

static void demo_kleene_logic(void) {
    printf("=== Kleene K₃ Logic ===\n");

    trit a = TRIT_TRUE;
    trit b = TRIT_UNKNOWN;
    trit c = TRIT_FALSE;

    printf("  T AND T = %d (expect  1)\n", trit_and(a, a));
    printf("  T AND U = %d (expect  0)\n", trit_and(a, b));
    printf("  T AND F = %d (expect -1)\n", trit_and(a, c));
    printf("  T OR  U = %d (expect  1)\n", trit_or(a, b));
    printf("  U OR  F = %d (expect  0)\n", trit_or(b, c));
    printf("  NOT T   = %d (expect -1)\n", trit_not(a));
    printf("  NOT U   = %d (expect  0)\n", trit_not(b));
    printf("  NOT F   = %d (expect  1)\n", trit_not(c));
    printf("\n");
}

/* ---- Type Safety Demo ------------------------------------------------- */

static void demo_type_safety(void) {
    printf("=== Trit Type Safety (trit_checked) ===\n");

    int fault = 0;
    trit ok = trit_checked(1, &fault);
    printf("  trit_checked(1): value=%d, fault=%d (expect 1, 0)\n", ok, fault);

    fault = 0;
    trit bad = trit_checked(42, &fault);
    printf("  trit_checked(42): value=%d, fault=%d (expect 0, 1)\n", bad, fault);

    fault = 0;
    trit neg = trit_checked(-1, &fault);
    printf("  trit_checked(-1): value=%d, fault=%d (expect -1, 0)\n", neg, fault);
    printf("\n");
}

/* ---- 2-Bit Packed Encoding Demo --------------------------------------- */

static void demo_packed_encoding(void) {
    printf("=== 2-Bit Packed Encoding (trit2) ===\n");

    trit2_reg32 reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    printf("  Splat(U): all 32 positions = Unknown\n");

    trit2_reg32_set(&reg, 0, TRIT2_TRUE);
    trit2_reg32_set(&reg, 5, TRIT2_FALSE);
    trit2_reg32_set(&reg, 31, TRIT2_TRUE);

    printf("  reg[0]  = %d (expect T=3)\n", trit2_reg32_get(&reg, 0));
    printf("  reg[5]  = %d (expect F=0)\n", trit2_reg32_get(&reg, 5));
    printf("  reg[15] = %d (expect U=1)\n", trit2_reg32_get(&reg, 15));
    printf("  reg[31] = %d (expect T=3)\n", trit2_reg32_get(&reg, 31));

    /* Popcnt: count True positions */
    int trues = 0;
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&reg, i) == TRIT2_TRUE) trues++;
    }
    printf("  True count = %d (expect 2)\n", trues);
    printf("\n");
}

/* ---- Casting Demo (trit_cast.h) --------------------------------------- */

static void demo_casting(void) {
    printf("=== Trit Casting ===\n");

    trit t = TRIT_TRUE;
    trit2 packed = trit_to_trit2(t);
    trit back = trit2_to_trit(packed);
    printf("  T → trit2 → trit: %d (expect 1)\n", back);

    t = TRIT_FALSE;
    int decoded = trit2_decode(trit_to_trit2(t));
    printf("  F → trit2 → decode: %d (expect -1)\n", decoded);

    t = TRIT_UNKNOWN;
    decoded = trit2_decode(trit_to_trit2(t));
    printf("  U → trit2 → decode: %d (expect 0)\n", decoded);
    printf("\n");
}

/* ---- Bulk SIMD-Style Operations --------------------------------------- */

static void demo_simd(void) {
    printf("=== Bulk SIMD Operations ===\n");

    const int N = 4;
    trit2_reg32 a[4], b[4], result[4];

    for (int i = 0; i < N; i++) {
        a[i] = trit2_reg32_splat(TRIT2_TRUE);
        b[i] = trit2_reg32_splat(TRIT2_FALSE);
    }

    trit2_reg32_and_bulk(result, a, b, N);
    printf("  AND_BULK(T,F)[0] = %d (expect F=0)\n",
           trit2_reg32_get(&result[0], 0));

    trit2_reg32_or_bulk(result, a, b, N);
    printf("  OR_BULK(T,F)[0]  = %d (expect T=3)\n",
           trit2_reg32_get(&result[0], 0));

    trit2_reg32_not_bulk(result, a, N);
    printf("  NOT_BULK(T)[0]   = %d (expect F=0)\n",
           trit2_reg32_get(&result[0], 0));
    printf("\n");
}

/* ---- Multi-Radix Instructions ----------------------------------------- */

static void demo_multiradix(void) {
    printf("=== Multi-Radix Instructions ===\n");

    multiradix_state_t mr;
    multiradix_init(&mr);

    /* DOT_TRIT: [T,T,T,...] · [T,T,T,...] */
    mr.regs[0] = trit2_reg32_splat(TRIT2_TRUE);
    mr.regs[1] = trit2_reg32_splat(TRIT2_TRUE);
    int dot = dot_trit(&mr, 0, 1);
    printf("  DOT(T,T) = %d (expect 32 = all products T)\n", dot);

    /* FFT_STEP (4 args: state, reg_in, reg_out, stride) */
    trit2_reg32_set(&mr.regs[0], 0, TRIT2_TRUE);
    trit2_reg32_set(&mr.regs[0], 1, TRIT2_FALSE);
    trit2_reg32_set(&mr.regs[0], 2, TRIT2_UNKNOWN);
    fft_step(&mr, 0, 0, 1);
    printf("  FFT_STEP(T,F,U): reg[0][0]=%d\n",
           trit2_reg32_get(&mr.regs[0], 0));

    /* RADIX_CONV: convert 42 to balanced ternary */
    radix_conv_to_ternary(&mr, 2, 42);
    printf("  RADIX_CONV(42): reg[2] loaded with balanced ternary\n");

    /* Telemetry */
    trit_lb_record(&mr);
    trit_lb_snapshot_t ss = trit_lb_snapshot(&mr);
    printf("  TRIT_LB: total_insns=%d, trit_ratio=%d%%\n",
           ss.total_insns, ss.trit_ratio_pct);
    printf("\n");
}

/* ---- Main ------------------------------------------------------------- */

int main(void) {
    printf("seT5 — End-to-End Clang Trit Demo\n");
    printf("==================================\n\n");

    demo_kleene_logic();
    demo_type_safety();
    demo_packed_encoding();
    demo_casting();
    demo_simd();
    demo_multiradix();

    printf("Demo complete. All operations use seT5 balanced ternary types.\n");
    printf("When compiled with seT5-Clang, __trit is a native builtin type.\n");
    return 0;
}
