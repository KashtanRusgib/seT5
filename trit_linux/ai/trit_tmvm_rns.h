/**
 * @file trit_tmvm_rns.h
 * @brief seT6 TMVM+RNS Integration — Residue-Domain Matrix-Vector Multiply
 *
 * Fuses Ternary Matrix-Vector Multiply (TMVM) with Residue Number System
 * (RNS) arithmetic to exploit carry-free, per-channel parallelism.
 * Each RNS channel computes an independent modular MAC, enabling
 * truncated multiplication with ~22% area savings.
 *
 * Key features:
 *   - RNS-domain dot product: per-channel modular MAC
 *   - Truncated MAC for approximate inference (top-k channels)
 *   - Area/energy model: quantified savings vs full CRT reconstruction
 *   - Works with any coprime moduli set from trit_rns.h
 *
 * @see trit_tmvm.h   for base TMVM accelerator
 * @see trit_rns.h    for RNS arithmetic core
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_TMVM_RNS_H
#define SET6_TRIT_TMVM_RNS_H

#include "set5/trit.h"
#include "set5/trit_rns.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TMVM_RNS_MAX_DIM       256   /**< Max vector/matrix dimension    */
#define TMVM_RNS_AREA_SAVE_PCT  22   /**< Area save vs full binary MAC   */
#define TMVM_RNS_ENERGY_PER_CH   3   /**< Attojoules per channel-MAC     */
#define TMVM_RNS_ENERGY_CRT     15   /**< aJ cost for CRT reconstruction */

/* ==== Types ============================================================= */

/**
 * @brief TMVM-RNS accelerator state.
 *
 * Stores a ternary matrix and vector in RNS residue domain,
 * performs per-channel MAC, then CRT-reconstructs the final
 * integer result.
 */
typedef struct {
    int  initialized;

    /* RNS context for modular channels */
    trit_rns_context_t rns_ctx;

    /* Matrix: each element stored as RNS residue vector */
    trit_rns_t matrix_rns[TMVM_RNS_MAX_DIM][TMVM_RNS_MAX_DIM];
    int  rows;
    int  cols;

    /* Vector: each element as RNS residue vector */
    trit_rns_t vector_rns[TMVM_RNS_MAX_DIM];
    int  vec_len;

    /* Integer result after CRT reconstruction */
    int  result[TMVM_RNS_MAX_DIM];
    int  result_len;

    /* Truncation control */
    int  active_channels;     /**< Channels used (truncated = fewer) */

    /* Statistics */
    int      total_channel_macs; /**< Total per-channel MACs      */
    int      crt_reconstructions;/**< Number of CRT operations     */
    int64_t  energy_aj;          /**< Energy consumed (attojoules) */
    int      area_save_pct;      /**< Computed area savings        */
} tmvm_rns_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize TMVM-RNS accelerator with a given RNS context.
 * @param st    State to initialize.
 * @param ctx   Initialized RNS context (moduli set determines channels).
 * @return 0 on success, -1 on error.
 */
int tmvm_rns_init(tmvm_rns_state_t *st, const trit_rns_context_t *ctx);

/**
 * @brief Load matrix elements into RNS residue form.
 *
 * Each trit value {-1, 0, +1} is encoded into RNS residue form:
 *   -1 → (m[i]-1) mod m[i] per channel,  0 → 0,  +1 → 1.
 *
 * @param st   State.
 * @param mat  Row-major trit matrix [rows * cols].
 * @param rows Number of rows.
 * @param cols Number of columns.
 * @return 0 on success, -1 on error.
 */
int tmvm_rns_load_matrix(tmvm_rns_state_t *st, const trit *mat,
                         int rows, int cols);

/**
 * @brief Load input vector into RNS residue form.
 * @param st  State.
 * @param vec Trit vector [len].
 * @param len Length (must equal cols).
 * @return 0 on success, -1 on error.
 */
int tmvm_rns_load_vector(tmvm_rns_state_t *st, const trit *vec, int len);

/**
 * @brief Execute RNS-domain matrix-vector multiply.
 *
 * For each row r, for each RNS channel k:
 *   acc_rns[k] = Σ (matrix_rns[r][c].residues[k] * vector_rns[c].residues[k])
 *              mod moduli[k]
 *
 * Then CRT-reconstructs the integer result per row.
 * If active_channels < count, only the first active_channels are used
 * (truncated MAC for approximate inference).
 *
 * @param st  State (matrix + vector must be loaded).
 * @return 0 on success, -1 on error.
 */
int tmvm_rns_execute(tmvm_rns_state_t *st);

/**
 * @brief Compute a single RNS-domain dot product.
 *
 * @param a    Array of RNS-encoded operands.
 * @param b    Array of RNS-encoded operands.
 * @param len  Vector length.
 * @param out  Output RNS accumulator.
 * @param ctx  RNS context.
 * @return 0 on success, -1 on error.
 */
int tmvm_rns_dot(const trit_rns_t *a, const trit_rns_t *b,
                 int len, trit_rns_t *out, const trit_rns_context_t *ctx);

/**
 * @brief Set number of active channels for truncated MAC.
 *
 * Fewer channels = faster but approximate. E.g., with {3,5,7},
 * using only channels {3,5} gives range 15 instead of 105.
 *
 * @param st       State.
 * @param channels Number of channels to use (1..ctx.count).
 * @return 0 on success, -1 on error.
 */
int tmvm_rns_set_truncation(tmvm_rns_state_t *st, int channels);

/**
 * @brief Get area savings percentage.
 * @param st  State after execution.
 * @return Area savings (0-100).
 */
int tmvm_rns_get_area_save(const tmvm_rns_state_t *st);

/**
 * @brief Get total energy consumed in attojoules.
 * @param st  State after execution.
 * @return Energy in aJ.
 */
int64_t tmvm_rns_get_energy(const tmvm_rns_state_t *st);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_TMVM_RNS_H */
