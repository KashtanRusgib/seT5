/*
 * seT5 Ternary Casting — Portable Runtime Helpers
 *
 * These implement the Kleene lattice embedding/projection at runtime
 * for stock compilers. A seT5-patched Clang would inline these as
 * intrinsics during CodeGen.
 *
 * AFP: "Three-Valued Logic" — embed: Bool->Trit, project: Trit->Bool (partial)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TRIT_CAST_H
#define SET5_TRIT_CAST_H

#include "set5/trit.h"
#include <assert.h>

/* ---- bool -> trit (lossless embedding) ---- */
static inline trit trit_from_bool(int b) {
    /* false(0) -> -1,  true(non-zero) -> +1 */
    return b ? TRIT_TRUE : TRIT_FALSE;
}

/* ---- trit -> bool (partial projection) ---- */
/*
 * Kleene lattice: project(U) is undefined.
 * This function asserts definite; use trit_to_bool_safe() for
 * conservative collapse (U->false).
 */
static inline int trit_to_bool_strict(trit v) {
    assert(v != TRIT_UNKNOWN &&
           "trit_to_bool_strict: cannot project 'unknown' to bool");
    return v == TRIT_TRUE;
}

/* ---- int -> trit (range-checked narrowing) ---- */
static inline trit trit_from_int(int v) {
    /* Clamp: values outside {-1,0,+1} -> unknown + fault */
    if (v < -1 || v > 1) return TRIT_UNKNOWN;
    return (trit)v;
}

/* ---- trit -> int (lossless widening) ---- */
static inline int trit_to_int(trit v) {
    return (int)v;
}

/* ---- Promotion: trit op int -> trit ---- */
/*
 * When trit appears in mixed arithmetic with int, promote int->trit.
 * This follows C's "usual arithmetic conversions" but with trit
 * having lower rank than short, so int narrows to trit.
 *
 * In practice: trit_and(t, trit_from_int(i))
 */

#endif /* SET5_TRIT_CAST_H */
