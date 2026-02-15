/**
 * @file trit_perplexity.h
 * @brief seT6 Perplexity Benchmark Engine for Ternary LLMs
 *
 * Perplexity estimation for evaluating ternary model quality against
 * full-precision baselines. Based on published results from:
 *
 *   - TernaryLLM (arXiv:2406.07177v1):
 *       WikiText2 PPL: FP16 6.10, DLT+OFF 11.22 (gap 5.12)
 *       C4 PPL:       FP16 9.20, DLT+OFF 13.38 (gap 4.18)
 *       PTB PPL:      FP16 10.60, DLT+OFF 16.29 (gap 5.69)
 *
 *   - TriLMs / Spectra (ICLR 2025):
 *       LAMBADA PPL @ 3.9B: TriLM 6.3, FloatLM 6.7 (TriLM wins!)
 *       ARC-E @3.9B: TriLM 74.2 vs FloatLM 72.4
 *       TriLM is the FIRST native ternary model to beat FP baseline
 *
 * PPL = exp(cross_entropy) = exp( -1/N Σ log p(w_i | context) )
 * Lower PPL = better model. log₂ variant: PPL = 2^H(W)
 *
 * Uses ×1000 fixed-point arithmetic consistent with seT6 conventions.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_PERPLEXITY_H
#define SET6_TRIT_PERPLEXITY_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define PPL_FP_SCALE           1000     /**< Fixed-point ×1000             */

/* Benchmark datasets (enum indices) */
#define PPL_DATASET_WIKITEXT2  0
#define PPL_DATASET_C4         1
#define PPL_DATASET_PTB        2
#define PPL_DATASET_LAMBADA    3
#define PPL_NUM_DATASETS       4

/* Model types */
#define PPL_MODEL_FP16         0        /**< Full-precision baseline       */
#define PPL_MODEL_TERNARY_DLT  1        /**< DLT-only ternarization        */
#define PPL_MODEL_TERNARY_OFF  2        /**< DLT + OFF distillation        */
#define PPL_MODEL_TRILM_NATIVE 3        /**< Native ternary (TriLM)        */
#define PPL_NUM_MODEL_TYPES    4

/* Published TernaryLLM PPL results (×1000) — Table 1 in paper */
#define PPL_REF_FP16_WIKI      6100     /**< FP16 Wiki2 PPL 6.10          */
#define PPL_REF_FP16_C4        9200     /**< FP16 C4 PPL 9.20             */
#define PPL_REF_FP16_PTB       10600    /**< FP16 PTB PPL 10.60           */
#define PPL_REF_DLT_OFF_WIKI   11220    /**< DLT+OFF Wiki2 PPL 11.22      */
#define PPL_REF_DLT_OFF_C4     13380    /**< DLT+OFF C4 PPL 13.38         */
#define PPL_REF_DLT_OFF_PTB    16290    /**< DLT+OFF PTB PPL 16.29        */

/* Published TriLM LAMBADA results (×1000) */
#define PPL_REF_TRILM_LAMBADA  6300     /**< TriLM 3.9B LAMBADA PPL 6.3   */
#define PPL_REF_FLOAT_LAMBADA  6700     /**< FloatLM 3.9B LAMBADA PPL 6.7 */

/* Quality thresholds (×1000) */
#define PPL_ACCEPTABLE_GAP     8000     /**< Max acceptable PPL gap = 8.0  */
#define PPL_EXCELLENT_GAP      3000     /**< Excellent gap < 3.0           */

/* Math constants (×1000) */
#define PPL_LN2_X1000          693      /**< ln(2) ×1000                   */
#define PPL_E_X1000            2718     /**< e ×1000                       */

#define PPL_MAX_MODELS         8        /**< Max model configs             */
#define PPL_MAX_TOKENS         1024     /**< Max tokens in a sequence      */

/* ==== Structures ======================================================== */

/**
 * Per-model PPL result on one dataset.
 */
typedef struct {
    int32_t  ppl_x1000;               /**< Perplexity ×1000               */
    int32_t  cross_entropy_x1000;      /**< Cross-entropy (nats) ×1000    */
    int32_t  bits_per_word_x1000;      /**< H(W) in bits ×1000            */
    int32_t  gap_to_fp16_x1000;        /**< PPL gap vs FP16 baseline      */
    int      dataset_id;               /**< Dataset index                  */
    int      model_type;               /**< Model type                     */
} ppl_result_t;

/**
 * Model configuration for PPL evaluation.
 */
typedef struct {
    int      model_type;               /**< PPL_MODEL_* enum              */
    int32_t  params_m;                 /**< Parameters in millions        */
    int32_t  loss_x1000;              /**< Training loss ×1000            */
    int32_t  ref_ppl[PPL_NUM_DATASETS]; /**< Reference PPL ×1000 if known */
    int      has_ref;                  /**< Has published reference data   */
} ppl_model_config_t;

/**
 * PPL benchmark state.
 */
typedef struct {
    int                initialized;
    ppl_model_config_t models[PPL_MAX_MODELS];
    int                model_count;
    ppl_result_t       results[PPL_MAX_MODELS * PPL_NUM_DATASETS];
    int                result_count;
    int32_t            best_ternary_ppl[PPL_NUM_DATASETS];
    int32_t            best_float_ppl[PPL_NUM_DATASETS];
} ppl_state_t;

/* ==== API =============================================================== */

/**
 * Initialize PPL benchmark state.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int ppl_init(ppl_state_t *st);

/**
 * Register a model for benchmarking.
 * @param st          Benchmark state.
 * @param model_type  PPL_MODEL_* constant.
 * @param params_m    Parameters in millions.
 * @param loss_x1000  Training loss ×1000 (used for PPL estimation).
 * @return Model index (≥0) on success, -1 on error.
 */
int ppl_add_model(ppl_state_t *st, int model_type, int32_t params_m,
                  int32_t loss_x1000);

/**
 * Set reference (published) PPL for a registered model.
 * @param st         State.
 * @param model_idx  Model index from ppl_add_model.
 * @param dataset    PPL_DATASET_* constant.
 * @param ppl_x1000  Published PPL ×1000.
 * @return 0 on success, -1 on error.
 */
int ppl_set_reference(ppl_state_t *st, int model_idx, int dataset,
                      int32_t ppl_x1000);

/**
 * Estimate PPL from cross-entropy loss.
 * PPL = exp(CE); uses integer exp approximation.
 * @param cross_entropy_x1000  Cross-entropy ×1000 (nats).
 * @return PPL ×1000.
 */
int32_t ppl_from_cross_entropy(int32_t cross_entropy_x1000);

/**
 * Estimate cross-entropy from bits-per-word.
 * CE = H(W) × ln(2)
 * @param bpw_x1000  Bits per word ×1000.
 * @return Cross-entropy ×1000 (nats).
 */
int32_t ppl_ce_from_bpw(int32_t bpw_x1000);

/**
 * Evaluate a model on a dataset. Uses reference PPL if available,
 * otherwise estimates from loss.
 * @param st         State.
 * @param model_idx  Model index.
 * @param dataset    Dataset index.
 * @param out        Result output.
 * @return 0 on success, -1 on error.
 */
int ppl_evaluate(ppl_state_t *st, int model_idx, int dataset,
                 ppl_result_t *out);

/**
 * Compute degradation ratio: ternary_PPL / fp16_PPL.
 * A ratio of 1.0 means no degradation.
 * @param ternary_ppl_x1000  Ternary model PPL ×1000.
 * @param fp16_ppl_x1000     FP16 baseline PPL ×1000.
 * @return Degradation ratio ×1000 (1000 = 1.0×).
 */
int32_t ppl_degradation_ratio(int32_t ternary_ppl_x1000,
                               int32_t fp16_ppl_x1000);

/**
 * Check if PPL gap is within acceptable bounds.
 * @param gap_x1000  Gap = (ternary_PPL - fp16_PPL) ×1000.
 * @return 1 if gap ≤ PPL_ACCEPTABLE_GAP, 0 otherwise.
 */
int ppl_gap_acceptable(int32_t gap_x1000);

/**
 * Check if ternary model beats float model (TriLM achievement).
 * @param ternary_ppl_x1000  Ternary PPL ×1000.
 * @param float_ppl_x1000    Float PPL ×1000.
 * @return 1 if ternary ≤ float (remarkable), 0 otherwise.
 */
int ppl_ternary_beats_float(int32_t ternary_ppl_x1000,
                             int32_t float_ppl_x1000);

/**
 * Find best ternary model for a dataset across all registered models.
 * @param st       State.
 * @param dataset  Dataset index.
 * @return Best ternary PPL ×1000, or -1 if no ternary models evaluated.
 */
int32_t ppl_best_ternary(ppl_state_t *st, int dataset);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_PERPLEXITY_H */
