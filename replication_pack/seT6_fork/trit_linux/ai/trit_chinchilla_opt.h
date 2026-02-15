/**
 * @file trit_chinchilla_opt.h
 * @brief seT6 Chinchilla-Optimal Ternary Training Scheduler
 *
 * Implements the TriLM training schedule from the TriLMs paper (ICLR 2025),
 * which uses a modified Chinchilla-optimal training recipe:
 *
 *   - Scaling law: L(N) = A / N^α + ε   (α = 0.26 for both TriLM & FloatLM)
 *   - TriLM: A=185, ε=1.76; FloatLM: A=159, ε=1.67
 *   - At halfway point (~150B tokens): reduce peak learning rate
 *   - At two-thirds point: remove weight decay (ternarization regularizes)
 *   - TriLM LR is 6× higher than FloatLM (e.g., 2.4e-3 vs 4.0e-4)
 *   - Batch size: 1M tokens (vs 2M for FloatLM)
 *
 * Also models the DLT scale/shift learning rate (0.1× weight LR)
 * and the complete Spectra suite configurations (99M–3.9B).
 *
 * Reference: TriLMs (ICLR 2025), TernaryLLM (arXiv:2406.07177v1)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_CHINCHILLA_OPT_H
#define SET6_TRIT_CHINCHILLA_OPT_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define CHI_FP_SCALE          1000    /**< Fixed-point ×1000               */

/* Scaling law constants (×1000) — from TriLMs Table 5 */
#define CHI_TRILM_A           185000  /**< A = 185.0 for TriLM             */
#define CHI_TRILM_ALPHA       260     /**< α = 0.260                       */
#define CHI_TRILM_EPS         1760    /**< ε = 1.760 (irreducible loss)    */
#define CHI_FLOAT_A           159000  /**< A = 159.0 for FloatLM           */
#define CHI_FLOAT_ALPHA       260     /**< α = 0.260 (same exponent!)      */
#define CHI_FLOAT_EPS         1670    /**< ε = 1.670                       */

/* Training schedule constants */
#define CHI_TOTAL_TOKENS_B    300     /**< 300B tokens total                */
#define CHI_HALFWAY_TOKENS_B  150     /**< LR reduction at halfway          */
#define CHI_TWOTHIRD_TOKENS_B 200     /**< Weight decay removal at 2/3      */
#define CHI_WARMUP_STEPS      500     /**< Warmup steps                     */
#define CHI_LR_DECAY_FINAL    100     /**< Final LR = 0.1× peak (cosine)   */
#define CHI_DLT_LR_RATIO      100    /**< DLT params LR = 0.1× weight LR  */

/* Spectra suite learning rates (×1e6 for integer representation) */
#define CHI_LR_99M_PEAK       2400    /**< 2.4e-3 ×1e6                     */
#define CHI_LR_99M_REDUCED    1500    /**< 1.5e-3 ×1e6 (after halfway)     */
#define CHI_LR_3B9_PEAK       1200    /**< 1.2e-3 ×1e6                     */
#define CHI_LR_3B9_REDUCED    800     /**< 8.0e-4 ×1e6                     */
#define CHI_FLOAT_LR_99M      400     /**< 4.0e-4 ×1e6 (FloatLM)          */

#define CHI_MAX_SCHEDULE       16     /**< Max schedule entries             */
#define CHI_BATCH_TRILM        1      /**< TriLM batch size (M tokens)      */
#define CHI_BATCH_FLOAT        2      /**< FloatLM batch size (M tokens)    */

/* ==== Structures ======================================================== */

/**
 * @brief Training schedule entry (one phase of training).
 */
typedef struct {
    int  start_step;        /**< Phase start step                        */
    int  end_step;          /**< Phase end step                          */
    int  lr_x1e6;           /**< Learning rate ×1e6                      */
    int  weight_decay;      /**< Weight decay active (1/0)               */
    int  dlt_lr_x1e6;       /**< DLT param learning rate ×1e6            */
} chi_phase_t;

/**
 * @brief Spectra model configuration with training params.
 */
typedef struct {
    int  params_m;          /**< Parameters in millions                  */
    int  hidden_dim;        /**< Hidden dimension                        */
    int  glu_dim;           /**< Gated Linear Unit dim                   */
    int  heads;             /**< Attention heads                         */
    int  layers;            /**< Transformer layers                      */
    int  peak_lr_x1e6;      /**< Initial peak LR ×1e6                    */
    int  reduced_lr_x1e6;   /**< Reduced LR (after halfway) ×1e6         */
    int  estimated_loss;    /**< Final loss ×1000                        */
    int  gap_to_float;      /**< Loss gap vs FloatLM ×1000               */
} chi_spectra_config_t;

/**
 * @brief Chinchilla optimizer state.
 */
typedef struct {
    int               initialized;
    chi_phase_t       schedule[CHI_MAX_SCHEDULE];
    int               phase_count;
    int               current_step;
    int               current_phase;

    chi_spectra_config_t spectra[9]; /**< 9 Spectra models               */
    int               spectra_count;

    int               total_steps;
    int               tokens_seen_b;  /**< Tokens consumed (billions)      */
} chi_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize Chinchilla optimizer.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int chi_init(chi_state_t *st);

/**
 * @brief Estimate TriLM loss using paper's scaling law.
 *
 * L(N) = A / N^α + ε  where A=185, α=0.26, ε=1.76
 *
 * @param params_m  Parameters in millions.
 * @return Estimated loss ×1000.
 */
int chi_trilm_loss(int params_m);

/**
 * @brief Estimate FloatLM loss using paper's scaling law.
 *
 * L(N) = A / N^α + ε  where A=159, α=0.26, ε=1.67
 *
 * @param params_m  Parameters in millions.
 * @return Estimated loss ×1000.
 */
int chi_float_loss(int params_m);

/**
 * @brief Compute loss gap: TriLM_loss - FloatLM_loss ×1000.
 * @param params_m  Parameters in millions.
 * @return Gap ×1000 (converges to ~90 at large N).
 */
int chi_loss_gap(int params_m);

/**
 * @brief Build Spectra training schedule for a given model size.
 *
 * Three phases:
 *   Phase 1: [0, halfway)  — peak LR, weight decay on
 *   Phase 2: [halfway, 2/3) — reduced LR, weight decay on
 *   Phase 3: [2/3, end)    — reduced LR, weight decay OFF
 *
 * @param st        State (schedule is stored here).
 * @param params_m  Model params in millions.
 * @param peak_lr   Peak learning rate ×1e6.
 * @param red_lr    Reduced learning rate ×1e6.
 * @return Number of phases on success, -1 on error.
 */
int chi_build_schedule(chi_state_t *st, int params_m,
                       int peak_lr, int red_lr);

/**
 * @brief Get the learning rate at a given step ×1e6.
 * @param st    State with schedule.
 * @param step  Training step.
 * @return LR ×1e6 (with cosine decay applied).
 */
int chi_get_lr_at_step(const chi_state_t *st, int step);

/**
 * @brief Check if weight decay should be active at given step.
 * @param st    State with schedule.
 * @param step  Training step.
 * @return 1 if active, 0 if removed (ternarization regularizes).
 */
int chi_weight_decay_active(const chi_state_t *st, int step);

/**
 * @brief Get DLT parameter LR at given step (0.1× weight LR).
 * @param st    State with schedule.
 * @param step  Training step.
 * @return DLT LR ×1e6.
 */
int chi_get_dlt_lr(const chi_state_t *st, int step);

/**
 * @brief Populate the full Spectra suite (9 configurations).
 * @param st  State (spectra[] is populated).
 * @return 0 on success, -1 on error.
 */
int chi_populate_spectra(chi_state_t *st);

/**
 * @brief Find crossover point where TriLM loss gap < threshold.
 * @param threshold_x1000  Max acceptable gap ×1000.
 * @return Crossover params in millions (0 if no crossover found).
 */
int chi_find_convergence(int threshold_x1000);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_CHINCHILLA_OPT_H */
