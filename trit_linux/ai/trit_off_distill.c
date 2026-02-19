/**
 * @file trit_off_distill.c
 * @brief seT6 Outlier-Friendly Feature Knowledge Distillation — implementation.
 *
 * Cosine-similarity mutual information maximization for ternary distillation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_off_distill.h"
#include <string.h>

/* ==== Helpers =========================================================== */

/** Integer square root (Newton's method). */
static int isqrt(int64_t x) {
    if (x <= 0) return 0;
    if (x == 1) return 1;
    int64_t r = x / 2;
    while (r > 0) {
        int64_t nr = (r + x / r) / 2;
        if (nr >= r) break;
        r = nr;
    }
    return (int)r;
}

/** Fixed-point natural log approximation (×1000).
 *  Input x is ×1000. Output is ln(x/1000) × 1000. */
static int fp_ln_off(int x_fp) {
    if (x_fp <= 0) return -7000;
    if (x_fp == 1000) return 0;

    int shifts = 0;
    int xn = x_fp;
    while (xn > 2000) { xn /= 2; shifts++; }
    while (xn < 500 && xn > 0) { xn *= 2; shifts--; }

    int64_t d = xn - 1000;
    int64_t d2 = (d * d) / 1000;
    int64_t d3 = (d2 * d) / 1000;
    int result = (int)(d - d2 / 2 + d3 / 3);
    result += shifts * 693;
    return result;
}

/** Absolute value helper */
static int off_abs(int v) { return (v < 0) ? -v : v; }

/* ==== Public API ======================================================== */

int off_init(off_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    st->temperature = OFF_DEFAULT_TEMP;
    return 0;
}

int off_set_temperature(off_state_t *st, int temp) {
    if (!st || !st->initialized) return -1;
    if (temp <= 0) return -1;
    st->temperature = temp;
    return 0;
}

int off_cosine_similarity(const int *teacher, const int *student, int dim) {
    if (!teacher || !student || dim <= 0) return 0;
    if (dim > OFF_MAX_DIM) dim = OFF_MAX_DIM;

    int64_t dot = 0;
    int64_t norm_t = 0;
    int64_t norm_s = 0;

    for (int i = 0; i < dim; i++) {
        int64_t t = teacher[i];
        int64_t s = student[i];
        dot += t * s;
        norm_t += t * t;
        norm_s += s * s;
    }

    /* cos_sim = dot / (||t|| × ||s||)
     * Scale: dot is ×1e6, norms are ×1e6, sqrt norms are ×1e3 */
    int64_t mag_t = isqrt(norm_t);
    int64_t mag_s = isqrt(norm_s);

    if (mag_t == 0 || mag_s == 0) return 0;

    /* dot is in scale ×1e6, mag product is ×1e6 → result ×1000 */
    int64_t denom = mag_t * mag_s;
    if (denom == 0) return 0;

    /* Scale dot up by 1000 for output precision */
    int cos_sim = (int)((dot * OFF_FP_SCALE) / denom);

    /* Clamp to [-1000, 1000] */
    if (cos_sim > OFF_FP_SCALE) cos_sim = OFF_FP_SCALE;
    if (cos_sim < -OFF_FP_SCALE) cos_sim = -OFF_FP_SCALE;

    return cos_sim;
}

int off_estimate_mi(int cos_sim) {
    /*
     * I(X;Y) ≈ -log(1 - cos²(X,Y))
     * cos_sim is ×1000, so cos² = (cos_sim² / 1000000) × 1000 = cos_sim²/1000
     */
    if (cos_sim < 0) cos_sim = -cos_sim;  /* MI uses |cos_sim| */
    if (cos_sim >= OFF_FP_SCALE) return 7000; /* Perfect correlation → max MI */
    if (cos_sim == 0) return 0; /* Zero correlation → zero MI */

    int64_t cos2 = ((int64_t)cos_sim * cos_sim) / OFF_FP_SCALE;  /* ×1000 */
    int one_minus_cos2 = OFF_FP_SCALE - (int)cos2;
    if (one_minus_cos2 <= 0) one_minus_cos2 = 1;

    /* MI = -ln(one_minus_cos2 / 1000) × 1000 */
    int mi = -fp_ln_off(one_minus_cos2);
    if (mi < 0) mi = 0;

    return mi;
}

int off_distill_step(off_state_t *st, const int *teacher,
                     const int *student, int dim) {
    if (!st || !st->initialized || !teacher || !student) return -1;
    if (dim <= 0 || dim > OFF_MAX_DIM) return -1;
    if (st->layer_count >= OFF_MAX_LAYERS) return -1;

    int idx = st->layer_count;
    off_layer_t *l = &st->layers[idx];

    l->dim = dim;
    l->cos_sim = off_cosine_similarity(teacher, student, dim);
    l->mutual_info = off_estimate_mi(l->cos_sim);
    l->off_loss = OFF_FP_SCALE - l->cos_sim;
    l->outlier_count = off_count_outliers(teacher, dim);

    st->total_outliers += l->outlier_count;
    st->layer_count++;

    /* Update running averages */
    int64_t sum_cos = 0, sum_mi = 0;
    for (int i = 0; i < st->layer_count; i++) {
        sum_cos += st->layers[i].cos_sim;
        sum_mi  += st->layers[i].mutual_info;
    }
    st->avg_cos_sim = (int)(sum_cos / st->layer_count);
    st->avg_mutual_info = (int)(sum_mi / st->layer_count);

    return idx;
}

int off_count_outliers(const int *features, int dim) {
    if (!features || dim <= 0) return 0;

    /* Compute mean |x| */
    int64_t abs_sum = 0;
    for (int i = 0; i < dim; i++) {
        abs_sum += off_abs(features[i]);
    }
    int mean_abs = (int)(abs_sum / dim);
    if (mean_abs == 0) return 0;

    /* Count values > 3 × mean */
    int threshold = mean_abs * 3;
    int outliers = 0;
    for (int i = 0; i < dim; i++) {
        if (off_abs(features[i]) > threshold) outliers++;
    }

    return outliers;
}

int off_get_retention(const off_state_t *st) {
    if (!st || !st->initialized || st->layer_count == 0) return 0;

    /* Retention = avg_MI / max_theoretical_MI × 1000
     * Max theoretical MI ≈ 7000 (from cos_sim = 1.0) */
    if (st->avg_mutual_info <= 0) return 0;
    int retention = (st->avg_mutual_info * OFF_FP_SCALE) / 7000;
    if (retention > OFF_FP_SCALE) retention = OFF_FP_SCALE;
    return retention;
}

int off_graded_truth(const int *features, int dim, int idx) {
    if (!features || dim <= 0 || idx < 0 || idx >= dim) return 0;

    /* Find L-infinity norm (max absolute value) */
    int max_abs = 0;
    for (int i = 0; i < dim; i++) {
        int a = (features[i] < 0) ? -features[i] : features[i];
        if (a > max_abs) max_abs = a;
    }

    if (max_abs == 0) return 0;

    /* Graded truth = |features[idx]| / max_abs × 1000 */
    int abs_val = (features[idx] < 0) ? -features[idx] : features[idx];
    return (abs_val * OFF_FP_SCALE) / max_abs;
}

int off_graded_mi(const int *teacher, const int *student, int dim) {
    if (!teacher || !student || dim <= 0) return 0;

    /* Compute truth-weighted cosine similarity:
     * For each dimension, weight by the graded truth magnitude.
     * This preserves gradient information from continuous activations. */
    int64_t dot = 0, mag_t = 0, mag_s = 0;

    /* Find L-inf norms for grading */
    int t_max = 0, s_max = 0;
    for (int i = 0; i < dim; i++) {
        int at = (teacher[i] < 0) ? -teacher[i] : teacher[i];
        int as_ = (student[i] < 0) ? -student[i] : student[i];
        if (at > t_max) t_max = at;
        if (as_ > s_max) s_max = as_;
    }
    if (t_max == 0 || s_max == 0) return 0;

    for (int i = 0; i < dim; i++) {
        /* Graded weights */
        int at = (teacher[i] < 0) ? -teacher[i] : teacher[i];
        int as_ = (student[i] < 0) ? -student[i] : student[i];
        int wt = (at * 1000) / t_max;
        int ws = (as_ * 1000) / s_max;

        /* Weighted inner product */
        int64_t tw = (int64_t)teacher[i] * wt / 1000;
        int64_t sw = (int64_t)student[i] * ws / 1000;
        dot += tw * sw;
        mag_t += tw * tw;
        mag_s += sw * sw;
    }

    if (mag_t == 0 || mag_s == 0) return 0;

    /* Integer sqrt approximation */
    int64_t denom_sq = mag_t * mag_s / (1000LL * 1000LL);
    int64_t denom = 1;
    while (denom * denom < denom_sq && denom < 1000000000LL) denom++;
    if (denom <= 0) return 0;

    int cos_g = (int)(dot / denom);
    if (cos_g > 1000) cos_g = 1000;
    if (cos_g < -1000) cos_g = -1000;

    /* MI ≈ -log(1 - cos²) ×1000
     * Using same estimation as off_estimate_mi */
    int cos_abs = (cos_g < 0) ? -cos_g : cos_g;
    int cos_sq = (cos_abs * cos_abs) / 1000;
    int one_minus = 1000 - cos_sq;
    if (one_minus <= 0) return 7000;
    if (one_minus >= 1000) return 0;

    /* -ln(x) ≈ (1-x)/x × 1000 for rough estimate */
    int mi = ((1000 - one_minus) * 1000) / one_minus;
    if (mi > 7000) mi = 7000;
    return mi;
}
