/*
 * seT6 Phase 1.1 Demo — Type-Safe Ternary Operations
 * Build: gcc -std=c99 -O2 -Iinclude -o demo/trit_type_demo demo/trit_type_demo.c
 *
 * Demonstrates casting rules and type safety from the Kleene lattice.
 *
 * SPDX-License-Identifier: GPL-2.0
 */
#pragma ternary

#include <stdio.h>
#include "set6/trit.h"
#include "set6/trit_type.h"
#include "set6/trit_cast.h"

static const char *trit_str(trit v) {
    switch (v) {
    case TRIT_FALSE:   return "F(-1)";
    case TRIT_UNKNOWN: return "U( 0)";
    case TRIT_TRUE:    return "T(+1)";
    default:           return "!ERR!";
    }
}

int main(void) {
    printf("=== seT6 Type System Demo ===\n\n");

    /* ---- bool -> trit (lossless embedding) ---- */
    printf("--- bool -> trit (embedding) ---\n");
    trit t_from_false = trit_from_bool(0);
    trit t_from_true  = trit_from_bool(1);
    printf("  false -> %s\n", trit_str(t_from_false));
    printf("  true  -> %s\n", trit_str(t_from_true));

    /* ---- trit -> bool (partial projection) ---- */
    printf("\n--- trit -> bool (projection) ---\n");
    printf("  T(+1) -> bool: %d\n", trit_to_bool_strict(TRIT_TRUE));
    printf("  F(-1) -> bool: %d\n", trit_to_bool_strict(TRIT_FALSE));
    printf("  U( 0) -> bool: (would assert — using safe collapse)\n");
    printf("  U( 0) -> safe: %d (conservative false)\n",
           trit_to_bool_safe(TRIT_UNKNOWN));

    /* ---- int -> trit (range-checked narrowing) ---- */
    printf("\n--- int -> trit (narrowing) ---\n");
    int test_vals[] = { -2, -1, 0, 1, 2, 42 };
    for (int i = 0; i < 6; i++) {
        trit t = trit_from_int(test_vals[i]);
        printf("  int(%2d) -> %s%s\n", test_vals[i], trit_str(t),
               (test_vals[i] < -1 || test_vals[i] > 1) ? " (CLAMPED)" : "");
    }

    /* ---- Range-checked construction ---- */
    printf("\n--- trit_checked (with fault detection) ---\n");
    int fault = 0;
    trit t1 = trit_checked(1, &fault);
    printf("  trit_checked(1):  %s, fault=%d\n", trit_str(t1), fault);
    trit t2 = trit_checked(5, &fault);
    printf("  trit_checked(5):  %s, fault=%d (OUT OF RANGE)\n", trit_str(t2), fault);

    /* ---- Kleene ops are valid; arithmetic is not ---- */
    printf("\n--- Valid Kleene operations ---\n");
    trit a = TRIT_TRUE, b = TRIT_UNKNOWN;
    printf("  T AND U = %s\n", trit_str(trit_and(a, b)));
    printf("  T OR  U = %s\n", trit_str(trit_or(a, b)));
    printf("  NOT U   = %s\n", trit_str(trit_not(b)));
    printf("  T => U  = %s\n", trit_str(trit_implies(a, b)));

    /* ---- Type safety: trit in conditions ---- */
    printf("\n--- Condition safety ---\n");
    trit cap_status = TRIT_UNKNOWN;
    /*
     * BAD (would error in seT6 Clang):
     *   if (cap_status) { ... }
     *
     * GOOD: explicit collapse
     */
    if (trit_to_bool_safe(cap_status)) {
        printf("  Access granted\n");
    } else {
        printf("  Access denied (unknown conservatively rejected)\n");
    }

    /* Strict check for definite values */
    trit verified = TRIT_TRUE;
    if (trit_is_definite(verified)) {
        printf("  Verified cap: %s -> bool: %d\n",
               trit_str(verified), trit_to_bool_strict(verified));
    }

    printf("\n=== All type checks passed ===\n");
    return 0;
}
