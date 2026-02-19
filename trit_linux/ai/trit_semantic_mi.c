/**
 * @file trit_semantic_mi.c
 * @brief seT6 Semantic Mutual Information — implementation.
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_semantic_mi.h"
#include <string.h>

/* ==== Integer Math Helpers ============================================== */

/** Integer log₂ ×1000 using lookup + interpolation. */
static int fp_log2(int x) {
    if (x <= 0) return 0;
    if (x == 1) return 0;
    /* Find integer log₂ */
    int log_int = 0, tmp = x;
    while (tmp > 1) { tmp >>= 1; log_int++; }
    /* Fractional part via linear interpolation */
    int lo = 1 << log_int;
    int hi = lo << 1;
    int frac = 0;
    if (hi > lo)
        frac = ((x - lo) * 1000) / (hi - lo);
    return log_int * 1000 + frac;
}

/** Integer square root. */
static int isqrt(int x) {
    if (x <= 0) return 0;
    int r = x, prev = 0;
    while (r != prev) {
        prev = r;
        r = (r + x / r) / 2;
    }
    return r;
}

/** Absolute value. */
static int abs_val(int x) { return (x < 0) ? -x : x; }

/* ==== Public API ======================================================== */

int smi_init(smi_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int smi_shannon_entropy(int count_neg, int count_zero, int count_pos) {
    int total = count_neg + count_zero + count_pos;
    if (total <= 0) return 0;

    /* H = -Σ (n_i / total) × log₂(n_i / total)
     *   = log₂(total) - (1/total) × Σ n_i × log₂(n_i) */
    int log_total = fp_log2(total);
    int sum = 0;
    int counts[3] = { count_neg, count_zero, count_pos };

    for (int i = 0; i < 3; i++) {
        if (counts[i] > 0) {
            int log_ni = fp_log2(counts[i]);
            /* n_i × log₂(n_i) / total — use int64_t to prevent overflow */
            sum += (int)(((int64_t)counts[i] * log_ni) / total);
        }
    }

    int entropy = log_total - sum;
    if (entropy < 0) entropy = 0;
    return entropy;
}

int smi_differential_entropy(int variance_x1000) {
    if (variance_x1000 <= 0) return 0;

    /* H(W) = ½ log₂(2πeσ²)
     * = ½ × (log₂(2πe) + log₂(σ²))
     * 2πe ≈ 17.079, log₂(17.079) ≈ 4.094
     * σ² = variance_x1000 / 1000
     * log₂(σ²) = log₂(variance_x1000) - log₂(1000)
     */
    int log2_2pie = 4094;  /* log₂(2πe) ×1000 */
    int log2_var = fp_log2(variance_x1000);
    int log2_1000 = fp_log2(1000);  /* ~9966 */

    int h = (log2_2pie + log2_var - log2_1000) / 2;
    return h;
}

int smi_build_histogram(smi_histogram_t *hist, const int *weights,
                        int count, int num_bins) {
    if (!hist || !weights || count <= 0) return -1;
    if (num_bins <= 0 || num_bins > SMI_MAX_BINS) num_bins = SMI_MAX_BINS;

    memset(hist, 0, sizeof(*hist));
    hist->num_bins = num_bins;
    hist->total = count;

    /* Find min/max */
    int wmin = weights[0], wmax = weights[0];
    for (int i = 1; i < count; i++) {
        if (weights[i] < wmin) wmin = weights[i];
        if (weights[i] > wmax) wmax = weights[i];
    }

    int range = wmax - wmin;
    if (range == 0) {
        hist->bins[0] = count;
        return 0;
    }

    /* Bin weights — use int64_t to prevent overflow for wide ranges */
    for (int i = 0; i < count; i++) {
        int bin = (int)(((int64_t)(weights[i] - wmin) * (num_bins - 1)) / range);
        if (bin < 0) bin = 0;
        if (bin >= num_bins) bin = num_bins - 1;
        hist->bins[bin]++;
    }

    return 0;
}

int smi_histogram_entropy(const smi_histogram_t *hist) {
    if (!hist || hist->total <= 0) return 0;

    int log_total = fp_log2(hist->total);
    int sum = 0;

    for (int i = 0; i < hist->num_bins; i++) {
        if (hist->bins[i] > 0) {
            int log_ni = fp_log2(hist->bins[i]);
            sum += (int)(((int64_t)hist->bins[i] * log_ni) / hist->total);
        }
    }

    int entropy = log_total - sum;
    if (entropy < 0) entropy = 0;
    return entropy;
}

int smi_estimate_mi(smi_state_t *st, const int *x, const int *y, int count) {
    if (!st || !st->initialized || !x || !y || count <= 0) return -1;
    if (st->layer_count >= SMI_MAX_LAYERS) return -1;

    int idx = st->layer_count;

    /* Build marginal histograms */
    smi_histogram_t hx, hy;
    int nbins = 16;
    if (count < 16) nbins = count;
    smi_build_histogram(&hx, x, count, nbins);
    smi_build_histogram(&hy, y, count, nbins);

    int h_x = smi_histogram_entropy(&hx);
    int h_y = smi_histogram_entropy(&hy);

    /* Joint entropy approximation:
     * Build a combined histogram where bin = binX * nbins + binY */
    int wmin_x = x[0], wmax_x = x[0];
    int wmin_y = y[0], wmax_y = y[0];
    for (int i = 1; i < count; i++) {
        if (x[i] < wmin_x) wmin_x = x[i];
        if (x[i] > wmax_x) wmax_x = x[i];
        if (y[i] < wmin_y) wmin_y = y[i];
        if (y[i] > wmax_y) wmax_y = y[i];
    }
    int range_x = wmax_x - wmin_x;
    int range_y = wmax_y - wmin_y;
    if (range_x == 0) range_x = 1;
    if (range_y == 0) range_y = 1;

    /* Use a smaller number of joint bins to keep it tractable */
    int jbins = 8;
    if (count < 8) jbins = count;
    int joint_total = jbins * jbins;
    int joint_counts[64]; /* 8×8 max */
    memset(joint_counts, 0, sizeof(joint_counts));

    for (int i = 0; i < count; i++) {
        int bx = (int)(((int64_t)(x[i] - wmin_x) * (jbins - 1)) / range_x);
        int by = (int)(((int64_t)(y[i] - wmin_y) * (jbins - 1)) / range_y);
        if (bx < 0) bx = 0; if (bx >= jbins) bx = jbins - 1;
        if (by < 0) by = 0; if (by >= jbins) by = jbins - 1;
        joint_counts[bx * jbins + by]++;
    }

    /* Joint entropy */
    int log_count = fp_log2(count);
    int jsum = 0;
    for (int i = 0; i < joint_total; i++) {
        if (joint_counts[i] > 0) {
            jsum += (int)(((int64_t)joint_counts[i] * fp_log2(joint_counts[i])) / count);
        }
    }
    int h_xy = log_count - jsum;
    if (h_xy < 0) h_xy = 0;

    /* MI = H(X) + H(Y) - H(X,Y) */
    int mi = h_x + h_y - h_xy;
    if (mi < 0) mi = 0;

    st->layers[idx].entropy_x = h_x;
    st->layers[idx].entropy_y = h_y;
    st->layers[idx].joint_entropy = h_xy;
    st->layers[idx].mutual_info = mi;
    st->layer_count++;

    /* Update running average */
    int sum_mi = 0;
    for (int i = 0; i < st->layer_count; i++)
        sum_mi += st->layers[i].mutual_info;
    st->avg_mi = sum_mi / st->layer_count;

    return idx;
}

int smi_graded_truth(int confidence, int max_conf) {
    if (max_conf <= 0) return 0;
    if (confidence <= 0) return 0;
    int graded = (confidence * 1000) / max_conf;
    if (graded > 1000) graded = 1000;
    return graded;
}

int smi_info_sufficient(int params_m, int threshold_bits) {
    if (params_m <= 0 || threshold_bits <= 0) return -1;
    /* Total info = params_M × 1e6 × 1.585 bits / 1e6 = params_M × 1585 / 1000
     * Use int64_t to avoid overflow for params_m > 1.35M, and add
     * +500 rounding to avoid boundary truncation (e.g. 3154*1585/1000). */
    int total_info_m = (int)(((int64_t)params_m * SMI_INFO_PER_TRIT + 500) / 1000);
    return (total_info_m >= threshold_bits) ? 1 : 0;
}

int smi_feature_alignment(smi_state_t *st, const int *teacher,
                          const int *student, int count) {
    if (!st || !st->initialized || !teacher || !student || count <= 0)
        return -1;

    /* Cosine similarity */
    int64_t dot = 0, norm_t = 0, norm_s = 0;
    for (int i = 0; i < count; i++) {
        dot    += (int64_t)teacher[i] * student[i];
        norm_t += (int64_t)teacher[i] * teacher[i];
        norm_s += (int64_t)student[i] * student[i];
    }
    int cos_sim = 0;
    if (norm_t > 0 && norm_s > 0) {
        int mag = isqrt((int)(norm_t / 1000)) * isqrt((int)(norm_s / 1000));
        if (mag > 0)
            cos_sim = (int)((dot / 1000) * 1000 / mag);
    }
    if (cos_sim > 1000) cos_sim = 1000;
    if (cos_sim < 0) cos_sim = 0;

    /* MI from estimate */
    int layer = smi_estimate_mi(st, teacher, student, count);
    int mi_norm = 0;
    if (layer >= 0 && st->layers[layer].entropy_x > 0) {
        mi_norm = (st->layers[layer].mutual_info * 1000) /
                  st->layers[layer].entropy_x;
        if (mi_norm > 1000) mi_norm = 1000;
    }

    /* Weighted combination: 60% cos_sim, 40% MI */
    int alignment = (cos_sim * 600 + mi_norm * 400) / 1000;
    if (layer >= 0)
        st->layers[layer].alignment_score = alignment;

    return alignment;
}

int smi_info_bottleneck(int mi_input, int mi_output, int beta_x1000) {
    /* IB = MI(X;T) - β × MI(T;Y) */
    return mi_input - (beta_x1000 * mi_output) / 1000;
}
