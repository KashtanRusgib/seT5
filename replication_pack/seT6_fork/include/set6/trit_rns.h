/**
 * @file trit_rns.h
 * @brief seT6 Residue Number System — Output-Parameter API
 *
 * Redesigned RNS with output-parameter style, ctx-last convention,
 * and PVT noise injection for resilience testing.
 * Moduli {3, 5, 7} give dynamic range M = 105.
 *
 * Features:
 *   1. trit_rns_init()         — CRT precompute (Mi, Mi_inv via mod_inverse)
 *   2. trit_to_rns()           — trit2_reg32 → RNS residues (output param)
 *   3. rns_to_trit()           — RNS → trit2_reg32 CRT reconstruction (output param)
 *   4. rns_add()               — carry-free per-channel addition (output param)
 *   5. rns_sub()               — carry-free per-channel subtraction (output param)
 *   6. rns_mul()               — carry-free per-channel multiplication (output param)
 *   7. rns_montgomery_mul()    — Montgomery REDC per channel (output param)
 *   8. rns_is_zero()           — fast zero detect across channels
 *   9. rns_validate()          — range & CRT consistency check
 *  10. rns_extend_moduli()     — dynamic moduli extension
 *  11. rns_apply_noise()       — PVT noise injection for resilience
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_RNS_H
#define SET6_TRIT_RNS_H

#include "set6/trit.h"
#include "set6/trit_emu.h"
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

/** Number of coprime moduli in the default RNS base. */
#define RNS_MODULI_COUNT   3

/** Maximum supported moduli (for rns_extend_moduli). */
#define RNS_MAX_MODULI     6

/** Dynamic range M = product of moduli. */
#define RNS_DYNAMIC_RANGE  105     /* 3 × 5 × 7 */

/** Half dynamic range for signed representation. */
#define RNS_HALF_RANGE     52      /* ⌊105/2⌋ */

/** Default coprime moduli (ternary-friendly). */
static const uint32_t rns_initial_moduli[RNS_MODULI_COUNT] = { 3, 5, 7 };

/* ==== Types ============================================================= */

/**
 * @brief RNS context with precomputed CRT constants.
 *
 * After trit_rns_init(), every conversion and arithmetic op
 * uses these cached constants — no recomputation at run-time.
 */
typedef struct {
    uint32_t moduli[RNS_MAX_MODULI]; /**< Coprime moduli               */
    uint32_t count;                   /**< Number of active moduli      */
    uint32_t M;                       /**< Product of all moduli        */
    uint32_t Mi[RNS_MAX_MODULI];     /**< Mi = M / moduli[i]           */
    uint32_t Mi_inv[RNS_MAX_MODULI]; /**< Mi^(-1) mod moduli[i]  (CRT) */
} trit_rns_context_t;

/**
 * @brief RNS residue vector — one residue per modulus channel.
 */
typedef struct {
    uint32_t residues[RNS_MAX_MODULI]; /**< r[i] = value mod moduli[i] */
} trit_rns_t;

/* ==== API =============================================================== */

/**
 * @brief Initialise RNS context: precompute M, Mi[], Mi_inv[].
 * @param ctx   Context to initialise.
 * @return 0 on success, -1 on error (NULL ctx, non-coprime moduli).
 */
int trit_rns_init(trit_rns_context_t *ctx);

/**
 * @brief Convert a trit2_reg32 packed register to an RNS residue vector.
 *
 * Interprets the first @p n_trits positions as a balanced-ternary
 * number:  value = Σ decode(trit[i]) × 3^i.  Each residue channel
 * is computed modularly via Horner's method.
 *
 * @param trit_vec  Source trit2_reg32 register.
 * @param n_trits   Number of trits to interpret (1..32).
 * @param rns_out   Output residue vector.
 * @param ctx       Initialised RNS context.
 */
void trit_to_rns(const trit2_reg32 *trit_vec, int n_trits,
                  trit_rns_t *rns_out, const trit_rns_context_t *ctx);

/**
 * @brief Reconstruct a trit2_reg32 from RNS residues via CRT.
 *
 * Produces a balanced-ternary representation in the low @p n_trits
 * positions of the output register (remaining trits are UNKNOWN).
 *
 * @param rns_in    Input residue vector.
 * @param n_trits   Number of output trit positions to fill (1..32).
 * @param trit_out  Output trit2_reg32 register.
 * @param ctx       Initialised RNS context.
 */
void rns_to_trit(const trit_rns_t *rns_in, int n_trits,
                  trit2_reg32 *trit_out, const trit_rns_context_t *ctx);

/**
 * @brief RNS addition: per-channel r[i] = (a[i]+b[i]) mod m[i].
 */
void rns_add(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx);

/**
 * @brief RNS subtraction: per-channel r[i] = (a[i]-b[i]) mod m[i].
 */
void rns_sub(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx);

/**
 * @brief RNS multiplication: per-channel r[i] = (a[i]*b[i]) mod m[i].
 */
void rns_mul(const trit_rns_t *a, const trit_rns_t *b,
              trit_rns_t *out, const trit_rns_context_t *ctx);

/**
 * @brief Montgomery modular multiplication in each RNS channel.
 *
 * For channel i, computes REDC(a[i] * b[i]) mod moduli[i]
 * using ternary-aligned radix R = next power-of-3 > moduli[i].
 *
 * @param a     First operand (in Montgomery form per channel).
 * @param b     Second operand (in Montgomery form per channel).
 * @param out   Product residue vector (Montgomery form).
 * @param ctx   Initialised RNS context.
 */
void rns_montgomery_mul(const trit_rns_t *a, const trit_rns_t *b,
                          trit_rns_t *out, const trit_rns_context_t *ctx);

/**
 * @brief Fast zero detection: true iff all active channels are zero.
 */
bool rns_is_zero(const trit_rns_t *rns, const trit_rns_context_t *ctx);

/**
 * @brief Validate an RNS residue vector: range and CRT consistency.
 * @return 0 on valid, -1 on error.
 */
int rns_validate(const trit_rns_t *rns, const trit_rns_context_t *ctx);

/**
 * @brief Dynamically extend the modulus set with a new coprime modulus.
 *
 * Adds @p new_modulus to the context, recomputes M, Mi[], Mi_inv[].
 *
 * @param ctx          RNS context.
 * @param new_modulus  New coprime modulus to add (must be coprime to all existing).
 * @return 0 on success, -1 if not coprime or max moduli reached.
 */
int rns_extend_moduli(trit_rns_context_t *ctx, uint32_t new_modulus);

/**
 * @brief Inject PVT-style noise into an RNS residue vector.
 *
 * For each channel, with probability @p noise_prob, replaces the residue
 * with a random value in [0, moduli[i]).  Uses rand() internally.
 *
 * @param rns         Residue vector to perturb (modified in-place).
 * @param noise_prob  Per-channel corruption probability [0.0, 1.0].
 * @param ctx         Initialised RNS context.
 */
void rns_apply_noise(trit_rns_t *rns, double noise_prob,
                       const trit_rns_context_t *ctx);

/* ==== Extended Moduli Sets (2026) ====================================== */

/** Mersenne-like moduli: {2^n-1, 2^n, 2^n+1} for LUT-free ops. */
#define RNS_MODSET_MERSENNE_4    3, 4, 5       /**< n=2: max range 60   */
#define RNS_MODSET_MERSENNE_8    7, 8, 9       /**< n=3: max range 504  */

/** Ternary-aligned moduli: powers of 3 ± offsets, coprime. */
#define RNS_MODSET_TERNARY       3, 13, 37     /**< range 1443          */

/** Abundant moduli: {2^n-1, 2^n, 2^n+1, 2^{2n}-1}. */
#define RNS_MODSET_ABUNDANT      3, 4, 5, 15   /**< range 900           */

/** Crypto-grade moduli: large coprime set for pairing. */
#define RNS_MODSET_CRYPTO        11, 13, 17, 19, 23  /**< range 1062347 */

/**
 * @brief Initialize RNS context with a custom moduli set.
 * @param ctx     Context to initialise.
 * @param moduli  Array of coprime moduli.
 * @param count   Number of moduli (1..RNS_MAX_MODULI).
 * @return 0 on success, -1 on error.
 */
int trit_rns_init_custom(trit_rns_context_t *ctx,
                         const uint32_t *moduli, uint32_t count);

/**
 * @brief Mixed-Radix System (MRS) conversion from RNS.
 *
 * Produces mixed-radix digits d[] such that:
 *   X = d[0] + d[1]*m[0] + d[2]*m[0]*m[1] + ...
 * O(k^2) but avoids large CRT intermediates.
 *
 * @param rns     Input residue vector.
 * @param digits  Output mixed-radix digits (one per modulus).
 * @param ctx     Initialised RNS context.
 * @return 0 on success, -1 on error.
 */
int rns_to_mrs(const trit_rns_t *rns, uint32_t *digits,
               const trit_rns_context_t *ctx);

/**
 * @brief Convert mixed-radix digits back to RNS.
 * @param digits  Mixed-radix digit array.
 * @param rns_out Output residue vector.
 * @param ctx     Initialised RNS context.
 * @return 0 on success, -1 on error.
 */
int rns_from_mrs(const uint32_t *digits, trit_rns_t *rns_out,
                 const trit_rns_context_t *ctx);

/**
 * @brief Montgomery modular exponentiation in RNS.
 *
 * Computes base^exp mod M using repeated REDC squaring.
 * Used for post-quantum crypto primitives.
 *
 * @param base    Base residue vector.
 * @param exp     Exponent (small positive integer).
 * @param out     Result residue vector.
 * @param ctx     Initialised RNS context.
 * @return 0 on success, -1 on error.
 */
int rns_montgomery_exp(const trit_rns_t *base, uint32_t exp,
                       trit_rns_t *out, const trit_rns_context_t *ctx);

/**
 * @brief Compute gcd(a, b) for coprimality checks.
 */
uint32_t rns_gcd_public(uint32_t a, uint32_t b);

/**
 * @brief Minimally-redundant RNS: add a redundant modulus for error detection.
 *
 * Adds a check modulus mR = next prime coprime to all existing moduli.
 * Enables single-residue error detection (side-channel resistance).
 *
 * @param ctx     Context to extend with redundant modulus.
 * @return 0 on success, -1 on error.
 */
int rns_add_redundant_check(trit_rns_context_t *ctx);

/**
 * @brief Detect and correct single-residue errors using redundant modulus.
 *
 * Requires that rns_add_redundant_check() was called first.
 *
 * @param rns         Residue vector (potentially corrupted).
 * @param corrected   Output corrected vector (or copy if no error).
 * @param ctx         Context with redundant modulus.
 * @return 0 if no error, 1 if corrected, -1 on uncorrectable.
 */
int rns_detect_correct(const trit_rns_t *rns, trit_rns_t *corrected,
                       const trit_rns_context_t *ctx);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_RNS_H */
