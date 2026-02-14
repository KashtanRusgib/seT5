/**
 * @file ternary_weight_quantizer.h
 * @brief seT5 Ternary Weight Quantizer (TWQ) — BitNet b1.58 Engine
 *
 * Maps neural network weight tensors to balanced ternary {-1, 0, +1}
 * using symmetric thresholding with learned scaling factors.
 *
 * Key features:
 *   - Threshold-based quantization: |w| > Δ → sign(w), else → 0
 *   - Configurable Δ factor (default 0.7 × mean|w|)
 *   - Asymmetric scaling: w_p for positive, w_n for negative weights
 *   - Sparsity analysis for N:M structured pruning
 *   - MAC replacement: ternary multiply → add/sub/skip
 *   - Layer-wise quantization statistics
 *
 * Hardware alignment:
 *   - Samsung DLFET-RM: maps to {0, Vdd/2, Vdd} levels
 *   - Huawei CN119652311A: carry-lookahead ternary accumulation
 *   - BitNet b1.58: 1.58-bit weight representation
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Ternary-Aware LLM Kernel
 * @see multiradix.h for DOT_TRIT accumulation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TERNARY_WEIGHT_QUANTIZER_H
#define SET5_TERNARY_WEIGHT_QUANTIZER_H

#include "set5/trit.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Maximum weight vector length for single-layer quantization */
#define TWQ_MAX_WEIGHTS     4096

/** Default threshold factor (0.7 × mean|w| as per BitNet/TTQ) */
#define TWQ_DEFAULT_DELTA_FACTOR_NUM  7
#define TWQ_DEFAULT_DELTA_FACTOR_DEN  10

/** Quantization modes */
typedef enum {
    TWQ_MODE_SYMMETRIC,    /**< Single threshold Δ, wp = wn */
    TWQ_MODE_ASYMMETRIC,   /**< Separate wp, wn scaling */
    TWQ_MODE_STOCHASTIC    /**< Probabilistic rounding near threshold */
} twq_mode_t;

/* ==== Structures ======================================================= */

/**
 * @brief Quantization configuration.
 */
typedef struct {
    twq_mode_t  mode;          /**< Quantization mode */
    int         delta_num;     /**< Threshold factor numerator (e.g. 7) */
    int         delta_den;     /**< Threshold factor denominator (e.g. 10) */
    int         wp_scale;      /**< Positive weight scaling (×1000, default 1000) */
    int         wn_scale;      /**< Negative weight scaling (×1000, default 1000) */
    uint32_t    rng_seed;      /**< PRNG seed for stochastic mode */
} twq_config_t;

/**
 * @brief Quantization statistics for a layer.
 */
typedef struct {
    int   total_weights;       /**< Total number of weights */
    int   positive_count;      /**< Weights quantized to +1 */
    int   zero_count;          /**< Weights quantized to 0 (pruned) */
    int   negative_count;      /**< Weights quantized to -1 */
    int   sparsity_permille;   /**< Fraction of zeros (0-1000) */
    int   mean_abs_x1000;      /**< Mean absolute weight × 1000 */
    int   threshold_x1000;     /**< Applied threshold Δ × 1000 */
    int   mac_savings_pct;     /**< % MAC ops eliminated (zeros) */
} twq_stats_t;

/**
 * @brief Quantized weight layer.
 */
typedef struct {
    trit          weights[TWQ_MAX_WEIGHTS]; /**< Quantized ternary weights */
    int           count;                     /**< Number of weights */
    twq_config_t  config;                    /**< Active config */
    twq_stats_t   stats;                     /**< Quantization statistics */
} twq_layer_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize a TWQ config with defaults.
 * @param cfg  Config to initialize.
 */
void twq_config_init(twq_config_t *cfg);

/**
 * @brief Quantize a floating-point weight array to ternary.
 *
 * Applies threshold: w_q = +1 if w > Δ, -1 if w < -Δ, 0 otherwise.
 * Integer weights are scaled by 1000 (millionths representation).
 *
 * @param layer    Output quantized layer.
 * @param weights  Input weights (×1000 fixed-point).
 * @param count    Number of weights.
 * @param cfg      Quantization config.
 * @return         0 on success, -1 on error.
 */
int twq_quantize(twq_layer_t *layer, const int32_t *weights, int count,
                 const twq_config_t *cfg);

/**
 * @brief Compute ternary dot product of two quantized layers.
 *
 * Since weights are {-1, 0, +1}, this reduces to additions only:
 *   dot = Σ (a[i] == 0 || b[i] == 0) ? 0 : (a[i] == b[i]) ? 1 : -1
 *
 * @param a    First quantized layer.
 * @param b    Second quantized layer (or input activations as trits).
 * @param len  Number of elements to process.
 * @return     Dot product value.
 */
int twq_ternary_dot(const trit *a, const trit *b, int len);

/**
 * @brief Ternary matrix-vector multiply (single output neuron).
 *
 * Computes out = W · x where W is ternary, x is ternary.
 * Each multiply becomes add/sub/skip.
 *
 * @param weights  Ternary weight row (length = in_features).
 * @param input    Ternary input vector (length = in_features).
 * @param in_features  Input dimension.
 * @return         Accumulated integer result.
 */
int twq_matvec_row(const trit *weights, const trit *input, int in_features);

/**
 * @brief Apply N:M structured sparsity enforcement.
 *
 * In each N-element block, keep only M highest-magnitude entries,
 * zero the rest. This maximizes hardware sparse-path utilization.
 *
 * @param layer  Quantized layer to sparsify (modified in-place).
 * @param n      Block size (e.g. 4).
 * @param m      Max non-zero per block (e.g. 2).
 * @return       Number of additional weights zeroed.
 */
int twq_enforce_sparsity(twq_layer_t *layer, int n, int m);

/**
 * @brief Compute energy savings estimate.
 *
 * Ternary MAC = add/sub only (no multiply). Returns estimated
 * energy ratio vs. FP16 baseline (×1000).
 *
 * Base: FP16 MAC ~= 15.5 pJ, Ternary add ~= 0.9 pJ
 * Additional savings from sparsity (zero-skip).
 *
 * @param stats  Layer quantization statistics.
 * @return       Energy ratio (e.g. 58 = 5.8% of FP16 energy).
 */
int twq_energy_ratio(const twq_stats_t *stats);

/**
 * @brief Dequantize ternary weights back to fixed-point.
 *
 * Applies scaling: w_out = trit × (wp or wn) depending on sign.
 *
 * @param out      Output fixed-point values (×1000).
 * @param layer    Quantized layer.
 * @return         Number of weights dequantized.
 */
int twq_dequantize(int32_t *out, const twq_layer_t *layer);

#ifdef __cplusplus
}
#endif

#endif /* SET5_TERNARY_WEIGHT_QUANTIZER_H */
