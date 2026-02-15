/**
 * @file trit_semantic_mi.h
 * @brief seT6 Semantic Mutual Information — Feature Alignment Engine
 *
 * Implements mutual information estimation for ternary feature alignment,
 * combining Shannon entropy, differential entropy for weight distributions,
 * and graded Łukasiewicz L∞ epistemic truth for ternary inference.
 *
 * Key features:
 *   - Shannon entropy: H(X) = -Σ p_i log₂(p_i)
 *   - Differential entropy for Gaussian weights: H(W) = ½ log₂(2πeσ²)
 *   - MI estimation: I(X;Y) = H(X) - H(X|Y) ≈ H(X) + H(Y) - H(X,Y)
 *   - Graded L∞ truth: t(x) maps continuous to multi-valued [0, 1000]
 *   - Feature alignment score for DLT/OFF integration
 *   - Information bottleneck metric for layer selection
 *
 * Theory (from TernaryLLM / Tequila / TriLMs):
 *   At scale, ternary weights carry sufficient information:
 *   info_per_trit = log₂(3) ≈ 1.585 bits
 *   For N params at 1.58 bits: total_info = N × 1.585
 *   Larger models → lower entropy → fewer bits needed per weight
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_SEMANTIC_MI_H
#define SET6_TRIT_SEMANTIC_MI_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define SMI_FP_SCALE          1000    /**< Fixed-point scale ×1000         */
#define SMI_MAX_BINS          64      /**< Max histogram bins              */
#define SMI_MAX_LAYERS        32      /**< Max tracked layers              */
#define SMI_LOG2_E_X1000      1443    /**< log₂(e) ×1000 = 1.4427         */
#define SMI_LN2_X1000         693     /**< ln(2) ×1000 = 0.6931           */
#define SMI_INFO_PER_TRIT     1585    /**< log₂(3) ×1000 = 1.585 bits     */
#define SMI_TWOPI_E_X1000     17079   /**< 2πe ×1000 = 17.079             */
#define SMI_EPSILON           1       /**< Avoid log(0)                    */
#define SMI_GRADED_LEVELS     3       /**< K₃ Łukasiewicz levels           */

/* ==== Structures ======================================================== */

/**
 * @brief Histogram for entropy estimation.
 */
typedef struct {
    int  bins[SMI_MAX_BINS];    /**< Bin counts                          */
    int  num_bins;              /**< Active bins                         */
    int  total;                 /**< Total samples                       */
} smi_histogram_t;

/**
 * @brief Per-layer MI tracking.
 */
typedef struct {
    int  entropy_x;         /**< H(X) ×1000 — source entropy            */
    int  entropy_y;         /**< H(Y) ×1000 — target entropy            */
    int  joint_entropy;     /**< H(X,Y) ×1000 — joint                   */
    int  mutual_info;       /**< I(X;Y) ×1000 = H(X) + H(Y) - H(X,Y)   */
    int  alignment_score;   /**< Feature alignment ×1000 [0, 1000]       */
    int  info_bottleneck;   /**< Bottleneck metric ×1000                 */
    int  graded_truth;      /**< L∞ graded truth ×1000                   */
} smi_layer_t;

/**
 * @brief Semantic MI engine state.
 */
typedef struct {
    int           initialized;
    smi_layer_t   layers[SMI_MAX_LAYERS];
    int           layer_count;
    int           avg_mi;             /**< Running average MI ×1000        */
    int           total_info_bits;    /**< Total information capacity      */
    int           sufficient;         /**< 1 if MI > threshold for all     */
} smi_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize semantic MI engine.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int smi_init(smi_state_t *st);

/**
 * @brief Compute Shannon entropy of a trit distribution ×1000.
 *
 * H(X) = -Σ p_i log₂(p_i), where p_i = count_i / total.
 * For ternary: max H = log₂(3) ≈ 1.585 bits.
 *
 * @param count_neg   Count of -1 trits.
 * @param count_zero  Count of 0 trits.
 * @param count_pos   Count of +1 trits.
 * @return Entropy ×1000 (e.g., 1585 = log₂(3) bits).
 */
int smi_shannon_entropy(int count_neg, int count_zero, int count_pos);

/**
 * @brief Compute differential entropy for Gaussian weights ×1000.
 *
 * H(W) = ½ log₂(2πeσ²) where σ is std deviation.
 *
 * @param variance_x1000  Weight variance ×1000.
 * @return Differential entropy ×1000 (can be negative).
 */
int smi_differential_entropy(int variance_x1000);

/**
 * @brief Build histogram from weight array.
 * @param hist     Output histogram.
 * @param weights  Input weights (fp ×1000).
 * @param count    Number of weights.
 * @param num_bins Number of bins to use (capped at SMI_MAX_BINS).
 * @return 0 on success, -1 on error.
 */
int smi_build_histogram(smi_histogram_t *hist, const int *weights,
                        int count, int num_bins);

/**
 * @brief Compute entropy of a histogram ×1000.
 * @param hist  Input histogram.
 * @return Entropy ×1000.
 */
int smi_histogram_entropy(const smi_histogram_t *hist);

/**
 * @brief Estimate mutual information between two weight arrays ×1000.
 *
 * I(X;Y) = H(X) + H(Y) - H(X,Y)
 * Uses histogram binning for estimation.
 *
 * @param st      Engine state.
 * @param x       First array (fp ×1000).
 * @param y       Second array (fp ×1000).
 * @param count   Number of elements.
 * @return Layer index (>=0) on success, -1 on error.
 */
int smi_estimate_mi(smi_state_t *st, const int *x, const int *y, int count);

/**
 * @brief Compute Łukasiewicz graded truth value ×1000.
 *
 * Maps a continuous confidence value to L∞ multi-valued logic:
 *   truth = clamp(confidence / max_confidence, 0, 1000)
 * For ternary inference, maps to {0, 500, 1000} buckets.
 *
 * @param confidence  Confidence value ×1000.
 * @param max_conf    Maximum confidence ×1000.
 * @return Graded truth ×1000 [0, 1000].
 */
int smi_graded_truth(int confidence, int max_conf);

/**
 * @brief Compute information sufficiency for ternary quantization.
 *
 * Checks if N params at 1.58 bits carry enough information
 * (total_info >= threshold_bits).
 *
 * @param params_m       Parameters in millions.
 * @param threshold_bits Minimum information threshold in bits (M).
 * @return 1 if sufficient, 0 if not. -1 on error.
 */
int smi_info_sufficient(int params_m, int threshold_bits);

/**
 * @brief Compute feature alignment score between teacher and student ×1000.
 *
 * Combines cosine similarity with MI to produce overall alignment.
 * alignment = (cos_sim × 600 + mi_norm × 400) / 1000
 *
 * @param st       Engine state.
 * @param teacher  Teacher features (fp ×1000).
 * @param student  Student features (fp ×1000).
 * @param count    Number of elements.
 * @return Alignment score ×1000 [0, 1000], -1 on error.
 */
int smi_feature_alignment(smi_state_t *st, const int *teacher,
                          const int *student, int count);

/**
 * @brief Compute information bottleneck metric ×1000.
 *
 * IB = MI(X;T) - β × MI(T;Y) where T is compressed representation.
 * Higher = more compression for same task performance.
 *
 * @param mi_input    MI(X;T) ×1000 — input representation MI.
 * @param mi_output   MI(T;Y) ×1000 — output task MI.
 * @param beta_x1000  Trade-off parameter ×1000.
 * @return IB metric ×1000.
 */
int smi_info_bottleneck(int mi_input, int mi_output, int beta_x1000);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_SEMANTIC_MI_H */
