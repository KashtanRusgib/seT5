/**
 * @file trit_type.h
 * @brief seT5 Ternary First-Class Type Support
 *
 * Provides compile-time detection of seT5 Clang (__SET5_TERNARY__)
 * and a range-checked constructor trit_checked() with fault flag.
 *
 * On stock compilers, falls back to the int8_t typedef from trit.h.
 * On seT5 Clang, `trit` is a builtin keyword and `__unknown` is
 * a builtin constant.
 *
 * @see trit.h for the core type definition
 * @see AFP "Three-Valued Logic" — domain restriction
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TRIT_TYPE_H
#define SET5_TRIT_TYPE_H

#include "set5/trit.h"

/* ---- Compile-time detection of seT5 Clang ---- */
#ifdef __SET5_TERNARY__
  /* 'trit' is a builtin keyword — nothing to define */
  /* __unknown is a builtin constant — nothing to define */
#else
  /* Fallback: trit.h already provides typedef int8_t trit */
#endif

/* ---- Range-checked trit construction ---- */

/*
 * Construct a trit with runtime validation.
 * Values outside {-1, 0, +1} trap to TRIT_UNKNOWN and set fault flag.
 *
 * AFP reference: "Three-Valued Logic" entry — domain restriction
 * ensures all operations stay within the Kleene lattice {F, U, T}.
 */
static inline trit trit_checked(int v, int *fault) {
    if (v < -1 || v > 1) {
        if (fault) *fault = 1;
        return TRIT_UNKNOWN; /* clamp out-of-range to unknown */
    }
    if (fault) *fault = 0;
    return (trit)v;
}

#endif /* SET5_TRIT_TYPE_H */
