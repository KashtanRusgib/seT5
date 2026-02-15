/**
 * @file trit_outlier_handle.c
 * @brief seT6 Outlier-Tolerant Ternary Arithmetic — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_outlier_handle.h"
#include <string.h>

/* ---- helpers ----------------------------------------------------------- */

static int32_t abs_val(int32_t x) { return x < 0 ? -x : x; }

/** Integer square root via Newton's method. */
static int32_t isqrt(int32_t n)
{
    if (n <= 0) return 0;
    int32_t x = n, y = (x + 1) / 2;
    while (y < x) { x = y; y = (x + n / x) / 2; }
    return x;
}

/* ---- API implementation ------------------------------------------------ */

int olh_init(olh_state_t *st, int num_channels, int mode)
{
    if (!st) return -1;
    if (num_channels <= 0 || num_channels > OLH_MAX_CHANNELS) return -1;
    if (mode < OLH_MODE_CLAMP || mode > OLH_MODE_STALL_RECAL) return -1;

    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    st->num_channels = num_channels;
    st->sigma_threshold_x1000 = OLH_SIGMA_THRESHOLD;
    st->default_mode = mode;
    return 0;
}

int olh_update_stats(olh_state_t *st, int channel,
                     const int32_t *values, int count)
{
    if (!st || !st->initialized || !values) return -1;
    if (channel < 0 || channel >= st->num_channels) return -1;
    if (count <= 0) return -1;

    olh_channel_stats_t *ch = &st->channels[channel];
    int outliers = 0;

    /* Compute mean */
    int64_t sum = 0, abs_sum = 0;
    for (int i = 0; i < count; i++) {
        sum += values[i];
        abs_sum += abs_val(values[i]);
    }
    int32_t new_mean = (int32_t)(sum / count);
    int32_t new_abs_mean = (int32_t)((abs_sum * 1000) / count);

    /* Compute variance */
    int64_t var_sum = 0;
    for (int i = 0; i < count; i++) {
        int64_t diff = values[i] - new_mean;
        var_sum += diff * diff;
    }
    int32_t new_var = (int32_t)((var_sum * 1000) / count);

    /* Update with exponential moving average if we have history.
     * EMA blend: new_mean_x1000 = 0.7 × old + 0.3 × new.
     * Use int64_t to prevent overflow in new_mean * 1000. */
    int64_t new_mean_scaled = (int64_t)new_mean * 1000;
    if (ch->sample_count > 0) {
        ch->mean_x1000 = (int32_t)((int64_t)ch->mean_x1000 * 700 / 1000
                                   + new_mean_scaled * 300 / 1000);
        ch->variance_x1000 = new_var;
        ch->abs_mean_x1000 = new_abs_mean;
    } else {
        ch->mean_x1000 = (int32_t)new_mean_scaled;
        ch->variance_x1000 = new_var;
        ch->abs_mean_x1000 = new_abs_mean;
        ch->min_val = values[0];
        ch->max_val = values[0];
    }

    /* Track min/max and count outliers */
    int32_t sigma = isqrt(ch->variance_x1000);  /* σ × √1000 ≈ σ×31.6 */
    /* Threshold: mean ± k*σ; compare in same scale */
    int32_t thresh = (int32_t)((int64_t)sigma * st->sigma_threshold_x1000 / 1000);

    for (int i = 0; i < count; i++) {
        if (values[i] < ch->min_val) ch->min_val = values[i];
        if (values[i] > ch->max_val) ch->max_val = values[i];

        /* Check outlier: |value - mean| > k*σ
         * Use int64_t to prevent values[i]*1000 overflow. */
        int32_t dev = (int32_t)abs_val((int64_t)values[i] * 1000 - ch->mean_x1000);
        if (thresh > 0 && dev > thresh) {
            outliers++;
            ch->outlier_count++;
        }
    }

    ch->sample_count += count;
    st->total_samples += count;
    st->total_outliers += outliers;

    return outliers;
}

int olh_is_outlier(olh_state_t *st, int channel, int32_t value)
{
    if (!st || !st->initialized) return -1;
    if (channel < 0 || channel >= st->num_channels) return -1;

    olh_channel_stats_t *ch = &st->channels[channel];
    if (ch->sample_count == 0) return 0; /* No stats yet */

    int32_t sigma = isqrt(ch->variance_x1000);
    int32_t thresh = (int32_t)((int64_t)sigma * st->sigma_threshold_x1000 / 1000);
    int32_t dev = (int32_t)abs_val((int64_t)value * 1000 - ch->mean_x1000);

    return (thresh > 0 && dev > thresh) ? 1 : 0;
}

int32_t olh_dlt_threshold(int32_t abs_mean_x1000)
{
    /* Δ = 0.7 × mean(|W|) */
    return (int32_t)((int64_t)abs_mean_x1000 * OLH_DLT_THRESHOLD_K / 1000);
}

int olh_compute_rescale(olh_state_t *st, int channel,
                        olh_rescale_params_t *out)
{
    if (!st || !st->initialized || !out) return -1;
    if (channel < 0 || channel >= st->num_channels) return -1;

    olh_channel_stats_t *ch = &st->channels[channel];
    memset(out, 0, sizeof(*out));
    out->mode = st->default_mode;

    /* Shift = mean (center distribution at 0) */
    out->shift = ch->mean_x1000 / 1000;

    /* DLT threshold */
    out->dlt_delta = olh_dlt_threshold(ch->abs_mean_x1000);

    /* Scale: map [min-shift, max-shift] → [-9841, +9841] */
    int32_t range = ch->max_val - ch->min_val;
    if (range <= 0) range = 1;

    /* Scale factor: trit_range / data_range */
    int32_t trit_range = OLH_TRIT_RANGE_MAX - OLH_TRIT_RANGE_MIN;
    out->scale_x1000 = (int32_t)((int64_t)trit_range * 1000 / range);

    /* Cap scale factor to avoid amplifying noise */
    if (out->scale_x1000 > 10000) out->scale_x1000 = 10000;
    if (out->scale_x1000 < 100) out->scale_x1000 = 100;

    /* Stall injection for recalibration mode */
    if (out->mode == OLH_MODE_STALL_RECAL) {
        out->stalls_injected = OLH_RECAL_CYCLES;
        st->total_stalls += OLH_RECAL_CYCLES;
    }

    return 0;
}

int32_t olh_apply_rescale(int32_t value, const olh_rescale_params_t *params)
{
    if (!params) return olh_clamp_trit(value);

    int32_t result;

    switch (params->mode) {
    case OLH_MODE_CLAMP:
        result = olh_clamp_trit(value);
        break;

    case OLH_MODE_SHIFT_SCALE:
    case OLH_MODE_STALL_RECAL:
        /* Apply DLT-style shift then scale */
        result = value - params->shift;
        result = (int32_t)((int64_t)result * params->scale_x1000 / 1000);
        result = olh_clamp_trit(result);
        break;

    default:
        result = olh_clamp_trit(value);
        break;
    }

    return result;
}

int32_t olh_clamp_trit(int32_t value)
{
    if (value > OLH_TRIT_RANGE_MAX) return OLH_TRIT_RANGE_MAX;
    if (value < OLH_TRIT_RANGE_MIN) return OLH_TRIT_RANGE_MIN;
    return value;
}

int32_t olh_info_loss(const int32_t *original, const int32_t *rescaled,
                      int count)
{
    if (!original || !rescaled || count <= 0) return -1;

    /* Info loss ≈ MSE / variance of original */
    int64_t sum_orig = 0, sum_sq_orig = 0, sum_sq_err = 0;
    for (int i = 0; i < count; i++) {
        sum_orig += original[i];
        sum_sq_orig += (int64_t)original[i] * original[i];
        int64_t err = rescaled[i] - original[i];
        sum_sq_err += err * err;
    }

    int64_t mean = sum_orig / count;
    int64_t var = sum_sq_orig / count - mean * mean;
    if (var <= 0) var = 1;

    /* Loss percentage ×1000 = (MSE / var) × 1000 */
    int64_t mse = sum_sq_err / count;
    int32_t loss_pct = (int32_t)(mse * 1000 / var);

    /* Cap at 1000 (100%) */
    if (loss_pct > 1000) loss_pct = 1000;
    return loss_pct;
}

int olh_info_loss_status(const olh_state_t *st)
{
    if (!st || !st->initialized) return -1;
    if (st->info_loss_x1000 >= OLH_INFO_LOSS_CRIT) return 2;
    if (st->info_loss_x1000 >= OLH_INFO_LOSS_WARN) return 1;
    return 0;
}

int32_t olh_outlier_rate(const olh_state_t *st)
{
    if (!st || !st->initialized) return -1;
    if (st->total_samples == 0) return 0;
    return (int32_t)((int64_t)st->total_outliers * 1000 / st->total_samples);
}
