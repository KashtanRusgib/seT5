/**
 * @file trit_rns.h
 * @brief seT6 Residue Number System (RNS) for Ternary-Compatible Arithmetic
 *
 * Implements RNS operations using ternary-friendly moduli {3, 5, 7}
 * (dynamic range 105 = 3×5×7):
 *   - Forward RNS conversion (integer → residue tuple)
 *   - Chinese Remainder Theorem (CRT) reconstruction
 *   - RNS add, subtract, multiply — carry-free, parallel
 *   - Montgomery modular multiplication for crypto
 *   - Mixed-radix conversion (MRC) — sequential alternative to CRT
 *   - Overflow detection via base extension
 *
 * Theory: RNS decomposes Z_M into coprime channels Z_{m_i}, enabling
 * carry-free parallel arithmetic. For ternary, {3,5,7} are ideal:
 *   - 3 is the native ternary radix (direct mapping)
 *   - 5 ≡ 2 mod 3 (primitive root exists → NTT-compatible)
 *   - 7 ≡ 1 mod 3 (cube root of unity exists → FFT-compatible)
 *
 * Reference: 2026 RNS research — residue ops for modular mult,
 * compatible with {-1,0,1} without binary fallback.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_RNS_H
#define SET6_TRIT_RNS_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define RNS_NUM_MODULI       3        /* Number of coprime moduli           */
#define RNS_M0               3        /* Ternary-native modulus             */
#define RNS_M1               5        /* NTT-compatible modulus             */
#define RNS_M2               7        /* FFT-compatible modulus             */
#define RNS_DYNAMIC_RANGE    105      /* M = 3 × 5 × 7                     */
#define RNS_HALF_RANGE       52       /* ⌊M/2⌋ for signed representation   */

#define RNS_MAX_CHAIN        16       /* Max chained Montgomery ops         */

/* ==== Types ============================================================= */

/**
 * @brief RNS residue representation — a value in Z_105 as 3 residues.
 */
typedef struct {
    int r[RNS_NUM_MODULI];            /**< Residues: r[0] mod 3, r[1] mod 5, r[2] mod 7 */
} rns_residue_t;

/**
 * @brief CRT reconstruction constants (precomputed).
 */
typedef struct {
    int Mi[RNS_NUM_MODULI];           /**< Mi = M / mi                     */
    int yi[RNS_NUM_MODULI];           /**< yi = Mi^(-1) mod mi             */
    int M;                             /**< Dynamic range = product of mi   */
} rns_crt_t;

/**
 * @brief Montgomery context for modular multiplication.
 */
typedef struct {
    int modulus;                        /**< Target modulus N                */
    int R;                              /**< Montgomery radix R > N, gcd(R,N)=1 */
    int R_inv_mod_N;                    /**< R^(-1) mod N                   */
    int N_prime;                        /**< -N^(-1) mod R (for REDC)       */
    int R2_mod_N;                       /**< R^2 mod N (for toMontgomery)   */
    int ops_count;                      /**< Operations performed            */
} rns_montgomery_t;

/**
 * @brief RNS engine state.
 */
typedef struct {
    int           initialized;
    rns_crt_t     crt;                  /**< CRT constants                   */
    rns_montgomery_t mont;              /**< Montgomery context              */
    int           total_ops;            /**< Total RNS operations            */
    int           overflow_count;       /**< Overflow events detected        */
    int           ternary_direct;       /**< Ops using direct ternary (mod 3)*/
    int           binary_fallbacks;     /**< Binary fallback penalty counter */
} rns_state_t;

/* ==== API =============================================================== */

/** Initialize RNS engine with precomputed CRT constants. */
int rns_init(rns_state_t *st);

/** Forward: integer → RNS residues. Input must be in [-52, 52]. */
rns_residue_t rns_forward(const rns_state_t *st, int value);

/** Inverse: RNS residues → integer via CRT reconstruction. */
int rns_inverse(const rns_state_t *st, rns_residue_t res);

/** RNS addition (carry-free, per-channel mod). */
rns_residue_t rns_add(const rns_state_t *st, rns_residue_t a, rns_residue_t b);

/** RNS subtraction (carry-free, per-channel mod). */
rns_residue_t rns_sub(const rns_state_t *st, rns_residue_t a, rns_residue_t b);

/** RNS multiplication (carry-free, per-channel mod). */
rns_residue_t rns_mul(const rns_state_t *st, rns_residue_t a, rns_residue_t b);

/** RNS negation (per-channel: mi - ri). */
rns_residue_t rns_negate(const rns_state_t *st, rns_residue_t a);

/** Check if RNS value is zero (all residues zero). */
int rns_is_zero(rns_residue_t a);

/** Comparison via CRT inverse — returns -1, 0, +1 as signed compare. */
int rns_compare(const rns_state_t *st, rns_residue_t a, rns_residue_t b);

/** Mixed-Radix Conversion (MRC) — sequential inverse, no CRT. */
int rns_mrc_inverse(const rns_state_t *st, rns_residue_t res);

/** Overflow detection via range check after CRT reconstruction. */
int rns_detect_overflow(const rns_state_t *st, rns_residue_t a, rns_residue_t b);

/** Initialize Montgomery context for modulus N. */
int rns_montgomery_init(rns_montgomery_t *mont, int modulus);

/** Montgomery modular multiplication: a*b mod N (inputs in Montgomery form). */
int rns_montgomery_mul(rns_montgomery_t *mont, int a_mont, int b_mont);

/** Convert to Montgomery form: a * R mod N. */
int rns_to_montgomery(const rns_montgomery_t *mont, int a);

/** Convert from Montgomery form: a * R^(-1) mod N. */
int rns_from_montgomery(const rns_montgomery_t *mont, int a_mont);

/** Map trit array to RNS residue (interpret as balanced ternary number). */
rns_residue_t rns_from_trits(const rns_state_t *st, const trit *trits, int len);

/** Get ternary direct ratio (%) — how many ops used native mod-3 path. */
int rns_get_ternary_ratio(const rns_state_t *st);

/** Get binary fallback penalty count (should be 0 for pure ternary). */
int rns_get_binary_fallbacks(const rns_state_t *st);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_RNS_H */
