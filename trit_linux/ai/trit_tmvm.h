/**
 * @file trit_tmvm.h
 * @brief seT6 Ternary Matrix-Vector Multiply (TMVM) Accelerator
 *
 * User-space emulation of TWTM (Ternary Wallace Tree Multiplier)
 * architecture for AI/LLM dot-products. Uses trit2_reg32 SIMD
 * registers with sparsity-skip optimization (zero trits = free).
 *
 * Key features:
 *   - TMVM dot product with O(1) carry via NDR (Negative Differential
 *     Resistance) emulated reduction stages
 *   - Sparsity detection: skip zero-trit columns entirely
 *   - (3;2) compressor emulation: 3 inputs → 2 outputs per stage
 *     (vs 6 for binary), giving 88% PDP gain at register level
 *   - Batch matvec for full layer inference
 *   - Energy model tracking (aJ per MAC)
 *   - Integration with TWQ quantized weights
 *
 * @see multiradix.h for base multi-radix arithmetic
 * @see ternary_weight_quantizer.h for TWQ integration
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_TMVM_H
#define SET6_TRIT_TMVM_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

#define TMVM_MAX_DIM         256   /**< Max vector/matrix dimension */
#define TMVM_COMPRESSOR_RATIO  3   /**< (3;2) compressor: 3→2 reduction */
#define TMVM_PDP_GAIN_PCT     88   /**< Power-delay product gain vs binary */
#define TMVM_ENERGY_PER_MAC_AJ  5  /**< Attojoules per ternary MAC */
#define TMVM_ENERGY_BINARY_AJ  42  /**< Attojoules per binary MAC (reference) */

/* ==== Structures ======================================================= */

/**
 * @brief (3;2) compressor stage emulation.
 */
typedef struct {
    int   inputs[3];           /**< Three trit inputs */
    int   sum;                 /**< Sum output */
    int   carry;               /**< Carry output (NDR: O(1)) */
    int   stages_used;         /**< Reduction stages needed */
} tmvm_compressor_t;

/**
 * @brief TMVM accelerator state.
 */
typedef struct {
    int   initialized;

    /* Matrix storage (row-major, balanced ternary {-1,0,+1}) */
    trit  matrix[TMVM_MAX_DIM][TMVM_MAX_DIM];
    int   rows;
    int   cols;

    /* Vector storage */
    trit  vector[TMVM_MAX_DIM];
    int   vec_len;

    /* Output */
    int   result[TMVM_MAX_DIM]; /**< Accumulated integer results */
    int   result_len;

    /* Sparsity tracking */
    int   total_macs;          /**< Total MACs executed */
    int   sparse_skips;        /**< MACs skipped due to zero trits */
    int   compressor_stages;   /**< Total (3;2) compressor stages used */
    int   sparsity_pct;        /**< Observed sparsity (0-100) */

    /* Energy model */
    int64_t energy_aj;         /**< Total energy consumed (attojoules) */
    int64_t energy_binary_aj;  /**< Equivalent binary energy (for ratio) */
    int   pdp_gain_pct;        /**< Computed PDP gain vs binary */
} tmvm_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize TMVM accelerator.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int tmvm_init(tmvm_state_t *st);

/**
 * @brief Load a weight matrix (quantized ternary).
 * @param st    State.
 * @param mat   Row-major trit array [rows * cols].
 * @param rows  Number of rows.
 * @param cols  Number of columns.
 * @return 0 on success, -1 on error.
 */
int tmvm_load_matrix(tmvm_state_t *st, const trit *mat, int rows, int cols);

/**
 * @brief Load an input vector.
 * @param st   State.
 * @param vec  Trit array [len].
 * @param len  Vector length (must match cols).
 * @return 0 on success, -1 on mismatch.
 */
int tmvm_load_vector(tmvm_state_t *st, const trit *vec, int len);

/**
 * @brief Execute matrix-vector multiply with sparsity skip.
 *
 * For each row: result[r] = Σ matrix[r][c] * vector[c]
 * Skips MACs where either operand is zero.
 * Uses (3;2) compressor staging for partial sums.
 *
 * @param st  State (matrix + vector must be loaded).
 * @return 0 on success, -1 on error.
 */
int tmvm_execute(tmvm_state_t *st);

/**
 * @brief Execute a single (3;2) compressor stage.
 * @param comp  Compressor with inputs pre-loaded.
 * @return 0 on success.
 */
int tmvm_compress_32(tmvm_compressor_t *comp);

/**
 * @brief Compute ternary dot product of two trit vectors.
 *
 * Optimized path: skips zero trits entirely.
 *
 * @param a    First trit vector.
 * @param b    Second trit vector.
 * @param len  Length.
 * @param skips  Output: number of zero-skips.
 * @return Dot product (integer).
 */
int tmvm_dot_sparse(const trit *a, const trit *b, int len, int *skips);

/**
 * @brief Compute energy efficiency vs binary.
 * @param st  State after execution.
 * @return PDP gain percentage (0-100).
 */
int tmvm_get_pdp_gain(const tmvm_state_t *st);

/**
 * @brief Get observed sparsity percentage.
 * @param st  State after execution.
 * @return Sparsity percentage (0-100).
 */
int tmvm_get_sparsity(const tmvm_state_t *st);

/**
 * @brief DLT-aware matrix-vector multiply.
 *
 * Quantizes a FP weight matrix using DLT thresholds, loads it, then
 * executes TMVM.  Reports how many weights were trapped (deadzone)
 * vs active.  Combines DLT quantization with TMVM sparsity skip.
 *
 * @param st         TMVM state.
 * @param weights    FP weight matrix [rows*cols] (×1000).
 * @param vec        Input trit vector [cols].
 * @param rows       Number of rows.
 * @param cols       Number of columns.
 * @param wp         DLT positive threshold (×1000).
 * @param wn         DLT negative threshold (×1000).
 * @param delta      DLT shift (×1000).
 * @return Number of trapped (zero) weights, or -1 on error.
 */
int tmvm_dlt_quant(tmvm_state_t *st, const int *weights, const trit *vec,
                   int rows, int cols, int wp, int wn, int delta);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_TMVM_H */
