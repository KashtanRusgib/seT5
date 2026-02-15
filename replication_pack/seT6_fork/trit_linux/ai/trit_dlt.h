/**
 * @file trit_dlt.h
 * @brief seT6 Dual Learnable Ternarization (DLT) — Trapping-Free Quantization
 *
 * Implements the core ideas from Tequila/TernaryLLM papers for ternary
 * weight quantization without deadzone trapping. Weights get stuck at 0
 * when gradients are uninformative; DLT avoids this via learnable
 * asymmetric thresholds (wp, wn) and shift (delta).
 *
 * Key features:
 *   - Dual threshold ternarization: separate positive/negative scales
 *   - Learnable shift parameter for asymmetric weight distributions
 *   - Anti-trapping gradient estimator (STE with informative correction)
 *   - Deadzone detection and escape mechanism
 *   - Per-layer quantization statistics
 *   - Integration with TWQ (Ternary Weight Quantizer) for weight packing
 *
 * Theory (from Tequila, arXiv:2406.07177):
 *   Q(w) = { +1  if w > wp + delta
 *          {  0  if wn + delta <= w <= wp + delta
 *          { -1  if w < wn + delta
 *   where wp, wn, delta are learnable per-layer parameters.
 *
 * Deadzone trapping occurs when weights cluster at 0 and gradients
 * ∂L/∂w ≈ 0 for quantized-zero weights. DLT corrects this by:
 *   1. Asymmetric thresholds that adapt to weight distribution
 *   2. Shift that handles non-zero-mean distributions
 *   3. Informative gradient: ∂Q/∂wp ∝ Σ I(w near threshold)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_DLT_H
#define SET6_TRIT_DLT_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define DLT_MAX_LAYER_DIM     4096    /**< Max weights per layer           */
#define DLT_FP_SCALE          1000    /**< Fixed-point scale (×1000)       */
#define DLT_DEFAULT_WP        500     /**< Default positive threshold ×1000*/
#define DLT_DEFAULT_WN       (-500)   /**< Default negative threshold ×1000*/
#define DLT_DEFAULT_DELTA     0       /**< Default shift ×1000             */
#define DLT_LEARN_RATE        10      /**< Learning rate ×1000 = 0.010     */
#define DLT_TRAP_WINDOW       50      /**< Zone width for trapping detect  */
#define DLT_MAX_LAYERS        64      /**< Max quantization layers         */
#define DLT_DELTA_P_K         700     /**< Δp = 0.7 × E[|w>0|] ×1000     */
#define DLT_DELTA_N_K         700     /**< Δn = 0.7 × E[|w<0|] ×1000     */
#define DLT_REACTIVATE_KICK   100     /**< Threshold nudge for reactivation*/
#define DLT_TARGET_ZERO_PCT   200     /**< Target zero % ×10 = 20.0%      */

/* ==== Structures ======================================================== */

/**
 * @brief Per-layer DLT quantization state.
 */
typedef struct {
    int  wp;                /**< Positive threshold (fp ×1000)          */
    int  wn;                /**< Negative threshold (fp ×1000)          */
    int  delta;             /**< Asymmetric shift (fp ×1000)            */

    /* Learnable scale/shift (Tequila §3.2): sp shifts positive boundary,
     * sn shifts negative boundary independently. */
    int  sp;                /**< Positive shift (fp ×1000)              */
    int  sn;                /**< Negative shift (fp ×1000)              */

    /* Asymmetric thresholds from weight distribution:
     * Δp = 0.7 × E[|w| : w > 0],  Δn = 0.7 × E[|w| : w < 0] */
    int  delta_p;           /**< Positive asymmetric Δ (fp ×1000)      */
    int  delta_n;           /**< Negative asymmetric Δ (fp ×1000)      */

    /* Statistics */
    int  count_pos;         /**< Weights quantized to +1                */
    int  count_zero;        /**< Weights quantized to 0                 */
    int  count_neg;         /**< Weights quantized to -1                */
    int  trapped_count;     /**< Weights stuck in deadzone              */
    int  near_threshold;    /**< Weights near threshold boundaries      */
    int  total_weights;     /**< Total weights in layer                 */
    int  trapping_rate;     /**< Trapped / total × 1000                 */
    int  reactivated;       /**< Weights reactivated via STE kick       */

    /* STE gradient accumulators (per iteration) */
    int  grad_wp;           /**< ∂L/∂wp accumulator (fp ×1000)         */
    int  grad_wn;           /**< ∂L/∂wn accumulator (fp ×1000)         */
    int  grad_sp;           /**< ∂L/∂sp accumulator (fp ×1000)         */
    int  grad_sn;           /**< ∂L/∂sn accumulator (fp ×1000)         */
} dlt_layer_t;

/**
 * @brief DLT quantizer state (multi-layer).
 */
typedef struct {
    int          initialized;
    dlt_layer_t  layers[DLT_MAX_LAYERS];
    int          layer_count;
    int          total_trapped;    /**< Global trapped weight count     */
    int          total_escaped;    /**< Weights that escaped deadzone   */
    int          iterations;       /**< Training iterations completed   */
} dlt_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize DLT quantizer.
 * @param st  State to init.
 * @return 0 on success, -1 on NULL.
 */
int dlt_init(dlt_state_t *st);

/**
 * @brief Add a quantization layer with default thresholds.
 * @param st  DLT state.
 * @return Layer index (>=0), or -1 on error.
 */
int dlt_add_layer(dlt_state_t *st);

/**
 * @brief Quantize a weight array using DLT (dual learnable thresholds).
 *
 * Q(w) = +1 if w > wp + delta
 *       =  0 if wn + delta <= w <= wp + delta
 *       = -1 if w < wn + delta
 *
 * @param st       DLT state.
 * @param layer    Layer index.
 * @param weights  Input weights (fp ×1000).
 * @param out      Output trits.
 * @param count    Number of weights.
 * @return 0 on success, -1 on error.
 */
int dlt_quantize(dlt_state_t *st, int layer, const int *weights,
                 trit *out, int count);

/**
 * @brief Detect trapped weights in the deadzone.
 *
 * Counts weights stuck at 0 with |gradient| < DLT_TRAP_WINDOW.
 *
 * @param st       DLT state.
 * @param layer    Layer index.
 * @param weights  Weight array (fp ×1000).
 * @param count    Number of weights.
 * @return Number of trapped weights.
 */
int dlt_detect_trapped(dlt_state_t *st, int layer, const int *weights,
                       int count);

/**
 * @brief Update thresholds (wp, wn, delta) based on weight distribution.
 *
 * Adaptive step: moves thresholds toward regions of high weight density
 * to reduce trapping and balance +1/−1 assignments.
 *
 * @param st       DLT state.
 * @param layer    Layer index.
 * @param weights  Weight array (fp ×1000).
 * @param count    Number of weights.
 * @return 0 on success, -1 on error.
 */
int dlt_update_thresholds(dlt_state_t *st, int layer, const int *weights,
                          int count);

/**
 * @brief Get sparsity (fraction of zeros) for a layer ×1000.
 * @param st     DLT state.
 * @param layer  Layer index.
 * @return Sparsity ×1000 (e.g., 670 = 67.0%).
 */
int dlt_get_sparsity(const dlt_state_t *st, int layer);

/**
 * @brief Get quantization accuracy: fraction of weights that
 *        would round to their respective trit ×1000.
 * @param weights  Original weights (fp ×1000).
 * @param quant    Quantized trits.
 * @param count    Number of values.
 * @return Accuracy ×1000 (e.g., 950 = 95.0%).
 */
int dlt_quant_accuracy(const int *weights, const trit *quant, int count);

/**
 * @brief Compute asymmetric thresholds from weight distribution.
 *
 * Δp = 0.7 × E[|w| : w > 0], Δn = 0.7 × E[|w| : w < 0].
 * Stores results in layer's delta_p / delta_n fields.
 *
 * @param st       DLT state.
 * @param layer    Layer index.
 * @param weights  Weight array (fp ×1000).
 * @param count    Number of weights.
 * @return 0 on success, -1 on error.
 */
int dlt_compute_asymmetric(dlt_state_t *st, int layer, const int *weights,
                           int count);

/**
 * @brief STE (Straight-Through Estimator) gradient passthrough.
 *
 * For each weight, compute the STE gradient indicator:
 *   1 if weight is within the learnable zone (near a threshold boundary),
 *   0 otherwise (gradient is blocked).
 * Accumulates grad_wp, grad_wn, grad_sp, grad_sn in the layer.
 *
 * @param st       DLT state.
 * @param layer    Layer index.
 * @param weights  Weight array (fp ×1000).
 * @param grads    Upstream gradients (fp ×1000).
 * @param count    Number of weights.
 * @return Number of weights that received STE passthrough.
 */
int dlt_ste_gradient(dlt_state_t *st, int layer, const int *weights,
                     const int *grads, int count);

/**
 * @brief Reactivate trapped weights by nudging thresholds.
 *
 * If trapping_rate > DLT_TARGET_ZERO_PCT, shrinks the deadzone by
 * DLT_REACTIVATE_KICK and counts reactivated weights.
 *
 * @param st       DLT state.
 * @param layer    Layer index.
 * @param weights  Weight array (fp ×1000).
 * @param count    Number of weights.
 * @return Number of reactivated weights (>= 0), or -1 on error.
 */
int dlt_reactivate(dlt_state_t *st, int layer, const int *weights, int count);

/**
 * @brief Get the trapping rate for a layer (× 1000).
 * @param st     DLT state.
 * @param layer  Layer index.
 * @return Trapping rate ×1000, or 0 on error.
 */
int dlt_get_trapping_rate(const dlt_state_t *st, int layer);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_DLT_H */
