/**
 * @file trit_cast.h
 * @brief seT5 Ternary Casting — Portable Runtime Helpers
 *
 * Implements the Kleene lattice embedding/projection at runtime:
 *   - embed:   bool -> trit  (lossless: false->-1, true->+1)
 *   - project: trit -> bool  (partial: unknown is undefined)
 *   - narrow:  int -> trit   (range-checked: clamp out-of-range)
 *   - widen:   trit -> int   (lossless)
 *
 * A seT5-patched Clang would inline these as intrinsics.
 * On stock compilers, these are static inline helpers.
 *
 * @see SemaCastTrit.cpp for Clang integration rules
 * @see AFP "Three-Valued Logic" — embed/project formalization
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
 * The canonical 2-arg trit_to_bool_strict(v, err) is in trit.h (VULN-30).
 * This 1-arg assert-on-UNKNOWN variant is preserved for code that
 * does not need the error-out parameter.
 */
#ifndef TRIT_TO_BOOL_STRICT_DEFINED
#define TRIT_TO_BOOL_STRICT_DEFINED
static inline int trit_to_bool_strict_assert(trit v) {
    assert(v != TRIT_UNKNOWN &&
           "trit_to_bool_strict_assert: cannot project 'unknown' to bool");
    return v == TRIT_TRUE;
}
#endif

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

/* ---- trit <-> trit2 bridge (trit.h <-> trit_emu.h) ---- */
/*
 * These functions bridge the scalar trit type (trit.h) with the
 * 2-bit packed emulation type (trit_emu.h), resolving the encoding
 * gap between the two header families.
 *
 * Scalar:  int8_t  {-1, 0, +1}
 * Packed:  uint8_t {0x00=F, 0x01=U, 0x03=T, 0x02=Fault}
 */

#include "set5/trit_emu.h"

/** @brief Convert scalar trit to 2-bit packed encoding. */
static inline trit2 trit_to_trit2(trit v) {
    switch (v) {
    case TRIT_FALSE:   return TRIT2_FALSE;
    case TRIT_UNKNOWN: return TRIT2_UNKNOWN;
    case TRIT_TRUE:    return TRIT2_TRUE;
    default:           return TRIT2_FAULT;
    }
}

/** @brief Convert 2-bit packed encoding back to scalar trit. */
static inline trit trit2_to_trit(trit2 p) {
    switch (p & 0x03) {
    case TRIT2_FALSE:   return TRIT_FALSE;
    case TRIT2_UNKNOWN: return TRIT_UNKNOWN;
    case TRIT2_TRUE:    return TRIT_TRUE;
    default:            return TRIT_UNKNOWN;  /* fault → Unknown (safe) */
    }
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
