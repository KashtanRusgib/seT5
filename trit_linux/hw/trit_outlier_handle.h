/**
 * @file trit_outlier_handle.h
 * @brief seT6 Outlier-Tolerant Ternary Arithmetic Engine
 *
 * Handles activation outliers that arise in LLM inference on ternary
 * processors. Combines insights from:
 *
 *   - ART-9: 9-trit word has limited range [-9841, +9841]; activations
 *     regularly exceed balanced-ternary range during transformer inference
 *   - TernaryLLM / DLT: outlier shift parameter γ absorbs distribution
 *     mean; threshold Δ = 0.7 × Σ|W|/N avoids hard clamping
 *   - Tequila: semantic MI drops when outliers get clipped — need
 *     adaptive rescaling to preserve information content
 *   - TSMC TMD: WSe₂ threshold noise ±0.1V maps to ~2% activation jitter
 *
 * Strategy:
 *   1. Detect outliers (>k×σ from mean)
 *   2. Adaptive rescale (shift + scale to fit trit range)
 *   3. Pipeline stall injection for recalibration cycles
 *   4. Error tracking (information loss metric)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_OUTLIER_HANDLE_H
#define SET6_TRIT_OUTLIER_HANDLE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define OLH_FP_SCALE          1000    /**< Fixed-point ×1000               */
#define OLH_MAX_CHANNELS      64      /**< Max activation channels         */
#define OLH_MAX_WINDOW        128     /**< Rolling statistics window        */

/* ART-9 ternary range */
#define OLH_TRIT_RANGE_MAX    9841    /**< Max 9-trit balanced value       */
#define OLH_TRIT_RANGE_MIN   (-9841)  /**< Min 9-trit balanced value       */

/* Outlier detection thresholds (×1000) */
#define OLH_SIGMA_THRESHOLD   3000    /**< Default: 3.0σ outlier boundary  */
#define OLH_DLT_THRESHOLD_K   700     /**< DLT Δ = 0.7 × mean(|W|)        */
#define OLH_JIT_PERCENT       20      /**< TMD jitter budget 2.0%          */

/* Rescaling modes */
#define OLH_MODE_CLAMP        0       /**< Hard clamp to trit range        */
#define OLH_MODE_SHIFT_SCALE  1       /**< DLT-style shift + scale         */
#define OLH_MODE_STALL_RECAL  2       /**< Pipeline stall + recalibrate    */

/* Stall injection */
#define OLH_RECAL_CYCLES      4       /**< Cycles to recalibrate pipeline  */
#define OLH_MAX_STALLS_PCT    50      /**< Max stall overhead 5.0%         */

/* Info loss */
#define OLH_INFO_LOSS_WARN    100     /**< Warn if >10.0% info lost        */
#define OLH_INFO_LOSS_CRIT    250     /**< Critical if >25.0% info lost    */

/* ==== Structures ======================================================== */

/**
 * Per-channel activation statistics (rolling window).
 */
typedef struct {
    int32_t mean_x1000;                /**< Running mean ×1000             */
    int32_t variance_x1000;            /**< Running variance ×1000         */
    int32_t min_val;                   /**< Min observed value              */
    int32_t max_val;                   /**< Max observed value              */
    int32_t abs_mean_x1000;            /**< Σ|x|/N ×1000 for DLT threshold */
    int     sample_count;              /**< Samples in window               */
    int     outlier_count;             /**< Outliers detected               */
} olh_channel_stats_t;

/**
 * Rescaling parameters for one pass.
 */
typedef struct {
    int32_t shift;                     /**< DLT γ — subtract before quant  */
    int32_t scale_x1000;              /**< Scaling factor ×1000            */
    int32_t dlt_delta;                /**< Δ = k × abs_mean               */
    int     mode;                      /**< OLH_MODE_* selected            */
    int     stalls_injected;           /**< Stall cycles added             */
} olh_rescale_params_t;

/**
 * Outlier handler state.
 */
typedef struct {
    int                initialized;
    olh_channel_stats_t channels[OLH_MAX_CHANNELS];
    int                 num_channels;
    int32_t             sigma_threshold_x1000;
    int                 default_mode;
    int32_t             total_outliers;
    int32_t             total_samples;
    int32_t             total_stalls;
    int32_t             info_loss_x1000;     /**< Accumulated info loss %   */
} olh_state_t;

/* ==== API =============================================================== */

/**
 * Initialize outlier handler.
 * @param st           State.
 * @param num_channels Number of activation channels.
 * @param mode         Default rescaling mode (OLH_MODE_*).
 * @return 0 on success, -1 on error.
 */
int olh_init(olh_state_t *st, int num_channels, int mode);

/**
 * Update running statistics for a channel with new activation values.
 * @param st       State.
 * @param channel  Channel index.
 * @param values   Activation values array.
 * @param count    Number of values.
 * @return Number of outliers detected, or -1 on error.
 */
int olh_update_stats(olh_state_t *st, int channel,
                     const int32_t *values, int count);

/**
 * Detect if a single value is an outlier for a given channel.
 * @param st       State.
 * @param channel  Channel index.
 * @param value    Activation value to check.
 * @return 1 if outlier, 0 if normal, -1 on error.
 */
int olh_is_outlier(olh_state_t *st, int channel, int32_t value);

/**
 * Compute DLT threshold: Δ = k × (Σ|W|/N).
 * @param abs_mean_x1000  Mean absolute value ×1000.
 * @return Threshold Δ.
 */
int32_t olh_dlt_threshold(int32_t abs_mean_x1000);

/**
 * Compute adaptive rescaling parameters.
 * @param st       State.
 * @param channel  Channel index.
 * @param out      Output rescaling parameters.
 * @return 0 on success, -1 on error.
 */
int olh_compute_rescale(olh_state_t *st, int channel,
                        olh_rescale_params_t *out);

/**
 * Apply rescaling to an activation value.
 * @param value   Raw activation value.
 * @param params  Rescaling parameters.
 * @return Rescaled value within trit range.
 */
int32_t olh_apply_rescale(int32_t value, const olh_rescale_params_t *params);

/**
 * Clamp value to 9-trit balanced ternary range.
 * @param value  Input value.
 * @return Clamped value in [-9841, +9841].
 */
int32_t olh_clamp_trit(int32_t value);

/**
 * Estimate information loss from rescaling (bits lost / bits total).
 * @param original   Array of original values.
 * @param rescaled   Array of rescaled values.
 * @param count      Number of values.
 * @return Info loss ×1000 (percentage, e.g. 150 = 15.0%).
 */
int32_t olh_info_loss(const int32_t *original, const int32_t *rescaled,
                      int count);

/**
 * Check if total info loss exceeds warning threshold.
 * @param st  State.
 * @return 0 = ok, 1 = warning, 2 = critical.
 */
int olh_info_loss_status(const olh_state_t *st);

/**
 * Get outlier rate (outliers / total) ×1000.
 * @param st  State.
 * @return Outlier percentage ×1000, or -1 on error.
 */
int32_t olh_outlier_rate(const olh_state_t *st);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_OUTLIER_HANDLE_H */
