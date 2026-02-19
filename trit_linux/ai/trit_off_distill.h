/**
 * @file trit_off_distill.h
 * @brief seT6 Outlier-Friendly Feature Knowledge Distillation (OFF)
 *
 * Implements cosine-similarity-based mutual information maximization
 * for ternary knowledge distillation. From Tequila/TernaryLLM:
 * OFF recovers information lost during quantization by aligning
 * feature distributions between teacher (float) and student (ternary)
 * using cosine similarity as a proxy for mutual information.
 *
 * Key features:
 *   - Cosine similarity between feature vectors (teacher vs student)
 *   - Mutual information estimation: I(X;Y) ≈ -log(1 - cos²(X,Y))
 *   - Outlier-friendly: cos_sim naturally handles activation outliers
 *     (common in LLM hidden states) without explicit scaling
 *   - Per-layer distillation loss tracking
 *   - Information retention metric: how much of teacher info is preserved
 *   - Distillation temperature parameter (softened targets)
 *
 * Theory:
 *   cos_sim(x, y) = (x · y) / (||x|| × ||y||)
 *   I(X;Y) = H(X) - H(X|Y)  [estimated via cos_sim]
 *   OFF_loss = 1.0 - cos_sim(teacher_features, student_features)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_OFF_DISTILL_H
#define SET6_TRIT_OFF_DISTILL_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define OFF_MAX_DIM           1024    /**< Max feature vector dimension    */
#define OFF_MAX_LAYERS        64      /**< Max distillation layers         */
#define OFF_FP_SCALE          1000    /**< Fixed-point scale               */
#define OFF_DEFAULT_TEMP      1000    /**< Default temperature ×1000 = 1.0 */
#define OFF_INFO_THRESHOLD    800     /**< Min acceptable MI (×1000 = 0.8) */

/* ==== Structures ======================================================== */

/**
 * @brief Per-layer distillation state.
 */
typedef struct {
    int  cos_sim;           /**< Cosine similarity ×1000 (0..1000)     */
    int  mutual_info;       /**< Estimated MI ×1000                    */
    int  off_loss;          /**< OFF loss ×1000 (= 1000 - cos_sim)    */
    int  outlier_count;     /**< Feature values exceeding 3σ           */
    int  dim;               /**< Feature dimension used                */
} off_layer_t;

/**
 * @brief OFF distillation engine state.
 */
typedef struct {
    int          initialized;
    off_layer_t  layers[OFF_MAX_LAYERS];
    int          layer_count;
    int          temperature;       /**< Distillation temperature ×1000 */
    int          avg_cos_sim;       /**< Running average cos_sim ×1000  */
    int          avg_mutual_info;   /**< Running average MI ×1000       */
    int          total_outliers;    /**< Total outlier activations seen  */
} off_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize OFF distillation engine.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int off_init(off_state_t *st);

/**
 * @brief Set distillation temperature.
 * @param st    OFF state.
 * @param temp  Temperature ×1000 (e.g., 2000 = 2.0).
 * @return 0 on success, -1 on error.
 */
int off_set_temperature(off_state_t *st, int temp);

/**
 * @brief Compute cosine similarity between two feature vectors.
 *
 * cos_sim(x, y) = Σ(x_i × y_i) / (√Σ(x_i²) × √Σ(y_i²))
 *
 * @param teacher  Teacher feature vector (fp ×1000).
 * @param student  Student feature vector (fp ×1000).
 * @param dim      Vector dimension.
 * @return Cosine similarity ×1000 (range [-1000, +1000]).
 */
int off_cosine_similarity(const int *teacher, const int *student, int dim);

/**
 * @brief Estimate mutual information from cosine similarity.
 *
 * I(X;Y) ≈ -log(1 - cos²(X,Y))
 * Higher cos_sim → higher MI → better distillation.
 *
 * @param cos_sim  Cosine similarity ×1000.
 * @return Estimated MI ×1000 (always >= 0).
 */
int off_estimate_mi(int cos_sim);

/**
 * @brief Run one distillation step: compare teacher and student features.
 *
 * Computes cos_sim, MI, OFF_loss, and outlier count for one layer.
 *
 * @param st       OFF state.
 * @param teacher  Teacher features (fp ×1000).
 * @param student  Student features (fp ×1000; typically quantized).
 * @param dim      Feature dimension.
 * @return Layer index used (>=0), or -1 on error.
 */
int off_distill_step(off_state_t *st, const int *teacher,
                     const int *student, int dim);

/**
 * @brief Count outlier activations in a feature vector.
 *
 * An outlier is any value with |x| > 3 × mean(|x|).
 * LLMs produce extreme activation outliers that disrupt MSE-based
 * distillation but are handled naturally by cosine similarity.
 *
 * @param features  Feature vector (fp ×1000).
 * @param dim       Vector dimension.
 * @return Number of outliers.
 */
int off_count_outliers(const int *features, int dim);

/**
 * @brief Get information retention: avg MI / max theoretical MI × 1000.
 * @param st  OFF state.
 * @return Retention ×1000.
 */
int off_get_retention(const off_state_t *st);

/**
 * @brief Compute graded truth value from continuous feature activations.
 *
 * Maps a continuous activation value to a graded truth in [0, 1000]
 * using the L-infinity norm (max norm). Graded truth preserves
 * gradient information that discrete {-1,0,+1} quantization destroys.
 *
 * From OFF/TernaryLLM: graded truth = |activation| / max(|activations|)
 *
 * @param features  Feature vector (fp ×1000).
 * @param dim       Vector dimension.
 * @param idx       Index of the feature to grade.
 * @return Graded truth ×1000 (range [0, 1000]).
 */
int off_graded_truth(const int *features, int dim, int idx);

/**
 * @brief Compute mutual information using graded L-infinity truth values.
 *
 * Enhanced MI that accounts for continuous truth values instead of
 * discrete ternary. Higher fidelity for LLM gradient estimation.
 *
 * I_graded(X;Y) ≈ -log(1 - (graded_cos)²)
 * where graded_cos uses truth-weighted inner product.
 *
 * @param teacher  Teacher features (fp ×1000).
 * @param student  Student features (fp ×1000).
 * @param dim      Vector dimension.
 * @return Graded MI ×1000.
 */
int off_graded_mi(const int *teacher, const int *student, int dim);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_OFF_DISTILL_H */
