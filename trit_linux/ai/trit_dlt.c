/**
 * @file trit_dlt.c
 * @brief seT6 Dual Learnable Ternarization — implementation.
 *
 * Trapping-free ternary quantization with learnable asymmetric
 * thresholds and deadzone escape mechanism.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_dlt.h"
#include <string.h>

/* ==== Public API ======================================================== */

int dlt_init(dlt_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int dlt_add_layer(dlt_state_t *st) {
    if (!st || !st->initialized) return -1;
    if (st->layer_count >= DLT_MAX_LAYERS) return -1;

    int idx = st->layer_count;
    dlt_layer_t *l = &st->layers[idx];
    memset(l, 0, sizeof(*l));
    l->wp = DLT_DEFAULT_WP;
    l->wn = DLT_DEFAULT_WN;
    l->delta = DLT_DEFAULT_DELTA;

    st->layer_count++;
    return idx;
}

int dlt_quantize(dlt_state_t *st, int layer, const int *weights,
                 trit *out, int count) {
    if (!st || !st->initialized || !weights || !out) return -1;
    if (layer < 0 || layer >= st->layer_count) return -1;
    if (count <= 0 || count > DLT_MAX_LAYER_DIM) return -1;

    dlt_layer_t *l = &st->layers[layer];

    int pos_thresh = l->wp + l->delta;   /* Upper threshold */
    int neg_thresh = l->wn + l->delta;   /* Lower threshold */

    l->count_pos = 0;
    l->count_zero = 0;
    l->count_neg = 0;
    l->near_threshold = 0;
    l->total_weights = count;

    for (int i = 0; i < count; i++) {
        int w = weights[i];

        if (w > pos_thresh) {
            out[i] = TRIT_TRUE;
            l->count_pos++;
        } else if (w < neg_thresh) {
            out[i] = TRIT_FALSE;
            l->count_neg++;
        } else {
            out[i] = TRIT_UNKNOWN;
            l->count_zero++;
        }

        /* Near threshold: within TRAP_WINDOW of either boundary */
        int dist_pos = (w > pos_thresh) ? (w - pos_thresh) : (pos_thresh - w);
        int dist_neg = (w > neg_thresh) ? (w - neg_thresh) : (neg_thresh - w);
        if (dist_pos <= DLT_TRAP_WINDOW || dist_neg <= DLT_TRAP_WINDOW) {
            l->near_threshold++;
        }
    }

    return 0;
}

int dlt_detect_trapped(dlt_state_t *st, int layer, const int *weights,
                       int count) {
    if (!st || !st->initialized || !weights) return 0;
    if (layer < 0 || layer >= st->layer_count) return 0;
    if (count <= 0) return 0;

    dlt_layer_t *l = &st->layers[layer];
    int pos_thresh = l->wp + l->delta;
    int neg_thresh = l->wn + l->delta;
    int trapped = 0;

    /*
     * A weight is "trapped" in the deadzone if:
     *   1. It quantizes to 0 (in the deadzone)
     *   2. It is far from either threshold (gradient ≈ 0)
     *
     * Far from threshold = distance > TRAP_WINDOW from both boundaries.
     * These weights get zero STE gradient and never escape.
     */
    for (int i = 0; i < count; i++) {
        int w = weights[i];

        /* Must be in deadzone */
        if (w >= neg_thresh && w <= pos_thresh) {
            int dist_pos = pos_thresh - w;
            int dist_neg = w - neg_thresh;
            int min_dist = (dist_pos < dist_neg) ? dist_pos : dist_neg;

            /* Trapped: far from both thresholds */
            if (min_dist > DLT_TRAP_WINDOW) {
                trapped++;
            }
        }
    }

    l->trapped_count = trapped;
    st->total_trapped += trapped;
    return trapped;
}

int dlt_update_thresholds(dlt_state_t *st, int layer, const int *weights,
                          int count) {
    if (!st || !st->initialized || !weights) return -1;
    if (layer < 0 || layer >= st->layer_count) return -1;
    if (count <= 0) return -1;

    dlt_layer_t *l = &st->layers[layer];

    /*
     * Adaptive threshold update:
     * 1. Compute weight mean and spread
     * 2. If too many weights trapped (>50% in deadzone), shrink deadzone
     * 3. Adjust delta toward weight mean (handle non-zero-mean distributions)
     * 4. Balance positive/negative assignments
     */

    /* Compute mean and counts in each region */
    long sum = 0;
    int n_pos = 0, n_neg = 0, n_zero = 0;
    int pos_thresh = l->wp + l->delta;
    int neg_thresh = l->wn + l->delta;

    for (int i = 0; i < count; i++) {
        sum += weights[i];
        if (weights[i] > pos_thresh) n_pos++;
        else if (weights[i] < neg_thresh) n_neg++;
        else n_zero++;
    }

    int mean = (int)(sum / count);

    /* Step 1: Adjust delta toward mean */
    int delta_step = (mean - l->delta) * DLT_LEARN_RATE / DLT_FP_SCALE;
    l->delta += delta_step;

    /* Step 2: If too many zeros (trapping), shrink deadzone */
    int zero_pct = (n_zero * 100) / count;
    if (zero_pct > 60) {
        /* Shrink: positive threshold down, negative threshold up */
        l->wp -= DLT_LEARN_RATE;
        l->wn += DLT_LEARN_RATE;

        /* Don't let them cross */
        if (l->wp < 50) l->wp = 50;     /* Minimum deadzone width */
        if (l->wn > -50) l->wn = -50;

        /* Track escapes */
        int prev_trapped = l->trapped_count;
        dlt_detect_trapped(st, layer, weights, count);
        int new_trapped = l->trapped_count;
        if (new_trapped < prev_trapped) {
            st->total_escaped += (prev_trapped - new_trapped);
        }
    }

    /* Step 3: Balance pos/neg — if imbalanced, shift thresholds */
    if (n_pos > 0 && n_neg > 0) {
        int ratio = (n_pos * DLT_FP_SCALE) / n_neg;
        if (ratio > 1500) {
            /* Too many positives: raise positive threshold */
            l->wp += DLT_LEARN_RATE / 2;
        } else if (ratio < 667) {
            /* Too many negatives: lower negative threshold */
            l->wn -= DLT_LEARN_RATE / 2;
        }
    }

    st->iterations++;
    return 0;
}

int dlt_get_sparsity(const dlt_state_t *st, int layer) {
    if (!st || !st->initialized) return 0;
    if (layer < 0 || layer >= st->layer_count) return 0;

    const dlt_layer_t *l = &st->layers[layer];
    if (l->total_weights == 0) return 0;

    return (l->count_zero * DLT_FP_SCALE) / l->total_weights;
}

int dlt_quant_accuracy(const int *weights, const trit *quant, int count) {
    if (!weights || !quant || count <= 0) return 0;

    int correct = 0;
    for (int i = 0; i < count; i++) {
        /* "Correct" = quantized direction matches sign of weight */
        if (quant[i] == TRIT_TRUE && weights[i] > 0) correct++;
        else if (quant[i] == TRIT_FALSE && weights[i] < 0) correct++;
        else if (quant[i] == TRIT_UNKNOWN &&
                 weights[i] >= -DLT_DEFAULT_WP &&
                 weights[i] <=  DLT_DEFAULT_WP) correct++;
    }

    return (correct * DLT_FP_SCALE) / count;
}

/* ==== Tequila Extensions: Asymmetric Thresholds + STE + Reactivation ==== */

static int iabs(int v) { return (v < 0) ? -v : v; }

int dlt_compute_asymmetric(dlt_state_t *st, int layer, const int *weights,
                           int count) {
    if (!st || !st->initialized || !weights) return -1;
    if (layer < 0 || layer >= st->layer_count) return -1;
    if (count <= 0) return -1;

    dlt_layer_t *l = &st->layers[layer];

    /* Δp = 0.7 × E[|w| : w > 0],  Δn = 0.7 × E[|w| : w < 0] */
    int64_t sum_pos = 0, sum_neg = 0;
    int n_pos = 0, n_neg = 0;

    for (int i = 0; i < count; i++) {
        if (weights[i] > 0) { sum_pos += weights[i]; n_pos++; }
        else if (weights[i] < 0) { sum_neg += iabs(weights[i]); n_neg++; }
    }

    if (n_pos > 0)
        l->delta_p = (int)((sum_pos * DLT_DELTA_P_K) / ((int64_t)n_pos * 1000));
    else
        l->delta_p = DLT_DEFAULT_WP;

    if (n_neg > 0)
        l->delta_n = (int)((sum_neg * DLT_DELTA_N_K) / ((int64_t)n_neg * 1000));
    else
        l->delta_n = iabs(DLT_DEFAULT_WN);

    return 0;
}

int dlt_ste_gradient(dlt_state_t *st, int layer, const int *weights,
                     const int *grads, int count) {
    if (!st || !st->initialized || !weights || !grads) return 0;
    if (layer < 0 || layer >= st->layer_count) return 0;
    if (count <= 0) return 0;

    dlt_layer_t *l = &st->layers[layer];

    /* Use asymmetric boundaries with shifts:
     *   pos_thresh = Δp + sp,   neg_thresh = -(Δn) + sn
     * STE passthrough: weight within DLT_TRAP_WINDOW of either threshold */
    int pos_thresh = l->delta_p + l->sp;
    int neg_thresh = -(l->delta_n) + l->sn;

    int passthrough = 0;
    l->grad_wp = 0;
    l->grad_wn = 0;
    l->grad_sp = 0;
    l->grad_sn = 0;

    for (int i = 0; i < count; i++) {
        int w = weights[i];
        int g = grads[i];

        int dist_pos = iabs(w - pos_thresh);
        int dist_neg = iabs(w - neg_thresh);

        if (dist_pos <= DLT_TRAP_WINDOW) {
            /* Near positive boundary → pass gradient to wp, sp */
            l->grad_wp += g;
            l->grad_sp += g;
            passthrough++;
        } else if (dist_neg <= DLT_TRAP_WINDOW) {
            /* Near negative boundary → pass gradient to wn, sn */
            l->grad_wn += g;
            l->grad_sn += g;
            passthrough++;
        }
        /* Else: inside deadzone and far from boundaries → STE blocks grad */
    }

    return passthrough;
}

int dlt_reactivate(dlt_state_t *st, int layer, const int *weights, int count) {
    if (!st || !st->initialized || !weights) return -1;
    if (layer < 0 || layer >= st->layer_count) return -1;
    if (count <= 0) return -1;

    dlt_layer_t *l = &st->layers[layer];

    /* Detect trapped weights first */
    int prev_trapped = l->trapped_count;
    dlt_detect_trapped(st, layer, weights, count);

    /* Compute trapping rate × 1000 */
    if (l->total_weights > 0)
        l->trapping_rate = (int)(((int64_t)l->trapped_count * 1000) / l->total_weights);
    else
        l->trapping_rate = 0;

    /* If trapping rate above target, shrink deadzone to free weights */
    if (l->trapping_rate > DLT_TARGET_ZERO_PCT) {
        /* Shrink positive threshold and raise negative threshold */
        l->wp -= DLT_REACTIVATE_KICK;
        l->wn += DLT_REACTIVATE_KICK;

        /* Clamp minimum deadzone */
        if (l->wp < 50) l->wp = 50;
        if (l->wn > -50) l->wn = -50;

        /* Also adjust asymmetric deltas */
        if (l->delta_p > DLT_REACTIVATE_KICK)
            l->delta_p -= DLT_REACTIVATE_KICK / 2;
        if (l->delta_n > DLT_REACTIVATE_KICK)
            l->delta_n -= DLT_REACTIVATE_KICK / 2;

        /* Re-detect to count how many escaped */
        int new_trapped = 0;
        int pos_thresh = l->wp + l->delta;
        int neg_thresh = l->wn + l->delta;

        for (int i = 0; i < count; i++) {
            int w = weights[i];
            if (w >= neg_thresh && w <= pos_thresh) {
                int dist_pos = pos_thresh - w;
                int dist_neg = w - neg_thresh;
                int min_dist = (dist_pos < dist_neg) ? dist_pos : dist_neg;
                if (min_dist > DLT_TRAP_WINDOW)
                    new_trapped++;
            }
        }

        int freed = prev_trapped - new_trapped;
        if (freed < 0) freed = 0;
        l->reactivated += freed;
        st->total_escaped += freed;
        l->trapped_count = new_trapped;

        return freed;
    }

    return 0; /* No reactivation needed */
}

int dlt_get_trapping_rate(const dlt_state_t *st, int layer) {
    if (!st || !st->initialized) return 0;
    if (layer < 0 || layer >= st->layer_count) return 0;
    return st->layers[layer].trapping_rate;
}
