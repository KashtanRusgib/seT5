/**
 * @file trit_compat.h
 * @brief seT5 Ternary Naming Compatibility Layer
 *
 * Bridges the naming gap between the kernel headers and the
 * compiler submodule:
 *
 *   Kernel (trit.h):       TRIT_FALSE (-1), TRIT_UNKNOWN (0), TRIT_TRUE (+1)
 *   Compiler (ternary.h):  TRIT_N (-1),     TRIT_Z (0),       TRIT_P (+1)
 *   Isabelle (TritKleene):  Neg,              Unk,              Pos
 *
 * All three share the same underlying representation (int8_t / signed char
 * with values -1, 0, +1), so this is purely a naming unification.
 *
 * Include this header to use either naming convention interchangeably.
 *
 * @see trit.h       — kernel naming (F/U/T)
 * @see ternary.h    — compiler naming (N/Z/P)
 * @see TritKleene.thy — proof naming (Neg/Unk/Pos)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TRIT_COMPAT_H
#define SET5_TRIT_COMPAT_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Compiler (ternary.h) → Kernel (trit.h) aliases ------------------- */
/* These allow code written with TRIT_N/Z/P to compile against trit.h     */

#ifndef TRIT_N
#define TRIT_N   TRIT_FALSE    /**< Negative / False / -1 */
#endif

#ifndef TRIT_Z
#define TRIT_Z   TRIT_UNKNOWN  /**< Zero / Unknown / 0 */
#endif

#ifndef TRIT_P
#define TRIT_P   TRIT_TRUE     /**< Positive / True / +1 */
#endif

/* ---- Proof (Isabelle) naming aliases ---------------------------------- */

#ifndef TRIT_NEG
#define TRIT_NEG TRIT_FALSE    /**< Isabelle: Neg */
#endif

#ifndef TRIT_UNK
#define TRIT_UNK TRIT_UNKNOWN  /**< Isabelle: Unk */
#endif

#ifndef TRIT_POS
#define TRIT_POS TRIT_TRUE     /**< Isabelle: Pos */
#endif

/* ---- Operation aliases ------------------------------------------------ */
/* Compiler uses consensus/accept_any; kernel uses and/or.                */
/* Both implement Kleene min/max, so they're identical.                    */

/** @brief Alias: consensus = Kleene AND (min) */
#define trit_consensus  trit_and

/** @brief Alias: accept_any = Kleene OR (max) */
#define trit_accept_any trit_or

/* ---- Conversion: named for clarity ------------------------------------ */

/** @brief Convert compiler trit (signed char) to kernel trit (int8_t). No-op. */
static inline trit trit_from_compiler(int v) {
    /* Both use -1/0/+1 encoding — just clamp */
    if (v < -1) return TRIT_FALSE;
    if (v > +1) return TRIT_TRUE;
    return (trit)v;
}

/** @brief Convert kernel trit to compiler trit. No-op (same encoding). */
static inline int trit_to_compiler(trit v) {
    return (int)v;
}

#ifdef __cplusplus
}
#endif

#endif /* SET5_TRIT_COMPAT_H */
