/**
 * @file trit_tekum_float.h
 * @brief seT6 Tekum Arithmetic — Balanced Ternary Tapered Precision Floats
 *
 * Implements the tekum number format from Hunhold (arXiv:2512.10964v1):
 *   - Balanced ternary real arithmetic with tapered precision
 *   - Rounding equals truncation (max error <0.5 ulp)
 *   - Sign derived from leading non-zero trit (no sign bit)
 *   - Regime/exponent/fraction decomposition with anchor function
 *   - NaR and ∞ as first-class values in the real wheel algebra
 *
 * The format stores n-trit (n even, n≥8) values as:
 *   θ(t) = sign(t) · (1 + f) · 3^e
 * where e comes from regime+exponent trits and f from fraction trits.
 *
 * All arithmetic is integer-only using ×1000 fixed-point internally.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_TEKUM_FLOAT_H
#define SET6_TRIT_TEKUM_FLOAT_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TEKUM_MAX_TRITS       32      /**< Maximum word width (trits)       */
#define TEKUM_MIN_TRITS        8      /**< Minimum word width (trits)       */
#define TEKUM_REGIME_TRITS     3      /**< Fixed regime field width         */
#define TEKUM_FP_SCALE      1000      /**< Fixed-point scale factor         */

/** Special marker values (in integer representation) */
#define TEKUM_NAR          (-999999)  /**< Not a Real                       */
#define TEKUM_INF           (999999)  /**< Infinity                         */
#define TEKUM_ZERO               (0)  /**< Zero                             */

/** Regime-to-exponent-trit-count mapping: c(r) = max(0, |r| - 2) */
#define TEKUM_MAX_REGIME        7     /**< Max regime value for 3 trits     */

/** Dynamic range limits (for n=8 tekum) */
#define TEKUM_EXPO_MAX_N8      18     /**< Max exponent for 8-trit tekum    */
#define TEKUM_EXPO_MIN_N8    (-18)    /**< Min exponent for 8-trit tekum    */

/* ==== Structures ======================================================== */

/**
 * @brief Decoded tekum value.
 */
typedef struct {
    int  sign;          /**< +1, -1, or 0                          */
    int  regime;        /**< Regime value r ∈ [-7, +7]             */
    int  exponent;      /**< Decoded exponent e                    */
    int  fraction_x1000;/**< Fraction f × 1000 ∈ (-500, 500)      */
    int  value_x1000;   /**< Full decoded value × 1000             */
    int  is_nar;        /**< 1 if NaR                               */
    int  is_inf;        /**< 1 if ∞                                 */
    int  is_zero;       /**< 1 if zero                              */
    int  n_trits;       /**< Word width                             */
} tekum_decoded_t;

/**
 * @brief Tekum word — compact trit-encoded representation.
 *
 * Each trit stored as int8_t: -1, 0, +1. Array is MSB-first.
 */
typedef struct {
    int8_t trits[TEKUM_MAX_TRITS]; /**< Trit array (MSB = index n-1)  */
    int    n;                       /**< Trit count (even, ≥ 8)        */
} tekum_word_t;

/**
 * @brief Tekum arithmetic engine state.
 */
typedef struct {
    int  initialized;
    int  default_width;      /**< Default word width (trits)           */
    int  trunc_is_round;     /**< 1 to confirm trunc=round property    */
    int  ops_performed;      /**< Total arithmetic ops counter         */
    int  nar_produced;       /**< NaR results counter                  */
    int  overflows;          /**< Overflow (→ ∞) counter               */
} tekum_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize tekum engine.
 * @param st    State to initialize.
 * @param width Default word width in trits (even, ≥ 8).
 * @return 0 on success, -1 on error.
 */
int tekum_init(tekum_state_t *st, int width);

/**
 * @brief Encode a fixed-point value (×1000) into a tekum word.
 * @param st     Engine state.
 * @param val_x1000  Value × 1000 to encode.
 * @param out    Output tekum word.
 * @return 0 on success, -1 on error.
 */
int tekum_encode(tekum_state_t *st, int val_x1000, tekum_word_t *out);

/**
 * @brief Decode a tekum word into its components.
 * @param st     Engine state.
 * @param word   Input tekum word.
 * @param out    Output decoded value.
 * @return 0 on success, -1 on error.
 */
int tekum_decode(tekum_state_t *st, const tekum_word_t *word,
                 tekum_decoded_t *out);

/**
 * @brief Negate a tekum word (trit-wise negation = value negation).
 * @param word  Input tekum word.
 * @param out   Output negated word.
 * @return 0 on success, -1 on error.
 */
int tekum_negate(const tekum_word_t *word, tekum_word_t *out);

/**
 * @brief Add two tekum words.
 * @param st   Engine state.
 * @param a    First operand.
 * @param b    Second operand.
 * @param out  Result.
 * @return 0 on success, -1 on error.
 */
int tekum_add(tekum_state_t *st, const tekum_word_t *a,
              const tekum_word_t *b, tekum_word_t *out);

/**
 * @brief Multiply two tekum words.
 * @param st   Engine state.
 * @param a    First operand.
 * @param b    Second operand.
 * @param out  Result.
 * @return 0 on success, -1 on error.
 */
int tekum_mul(tekum_state_t *st, const tekum_word_t *a,
              const tekum_word_t *b, tekum_word_t *out);

/**
 * @brief Truncate a tekum word to fewer trits (= rounding in balanced ternary).
 *
 * This is the key property: truncation IS rounding, with max error < 0.5 ulp.
 *
 * @param word     Input tekum word.
 * @param n_trits  Target width (even, ≥ 8, < word->n).
 * @param out      Output truncated word.
 * @return 0 on success, -1 on error.
 */
int tekum_truncate(const tekum_word_t *word, int n_trits, tekum_word_t *out);

/**
 * @brief Compute truncation error in ulp × 1000.
 *
 * For balanced ternary, this is guaranteed < 500 (= 0.5 ulp).
 *
 * @param original  Full-precision tekum.
 * @param truncated Truncated tekum.
 * @return Error in ulp × 1000, or -1 on error.
 */
int tekum_truncation_error(tekum_state_t *st,
                           const tekum_word_t *original,
                           const tekum_word_t *truncated);

/**
 * @brief Compare two tekum words.
 * @param a  First operand.
 * @param b  Second operand.
 * @return -1 if a<b, 0 if a==b, +1 if a>b.
 */
int tekum_compare(const tekum_word_t *a, const tekum_word_t *b);

/**
 * @brief Compute radix economy ratio × 1000.
 *
 * Ternary economy / binary economy. < 1000 means ternary wins.
 *
 * @param n  Value to evaluate.
 * @return Economy ratio × 1000.
 */
int tekum_radix_economy(int n);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_TEKUM_FLOAT_H */
