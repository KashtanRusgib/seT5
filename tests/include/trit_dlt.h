/**
 * @file trit_dlt.h
 * @brief Inline implementation of trit DLT (Tequila) operations.
 *
 * Shared by test_dlt_cntfet.c, test_ternary_pdfs.c, and test_papers.c.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_DLT_H
#define TRIT_DLT_H

#include "set5/trit.h"
#include <string.h>
#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ── Constants ───────────────────────────────────────────────────────── */

#define DLT_MAX_LAYERS    16
#define DLT_DEFAULT_WP    500
#define DLT_DEFAULT_WN    (-500)
#define DLT_DEFAULT_DELTA 0

/* ── Types ───────────────────────────────────────────────────────────── */

typedef struct {
    int sp;              /* positive threshold */
    int sn;              /* negative threshold */
    int delta_p;         /* asymmetric delta (positive side) */
    int delta_n;         /* asymmetric delta (negative side) */
    int delta;           /* symmetric delta */
    int wp;              /* positive weight boundary */
    int wn;              /* negative weight boundary */
    int total_weights;
    int count_pos;
    int count_neg;
    int count_zero;
    int trapped_count;
    int reactivated;
    int grad_wp;         /* STE gradient accumulator (positive) */
    int grad_wn;         /* STE gradient accumulator (negative) */
} dlt_layer_t;

typedef struct {
    dlt_layer_t layers[DLT_MAX_LAYERS];
    int         layer_count;
    int         iterations;
} dlt_state_t;

/* ── Helpers (internal) ──────────────────────────────────────────────── */

static inline int dlt__abs(int v) { return v < 0 ? -v : v; }

/* ── API ─────────────────────────────────────────────────────────────── */

/**
 * Initialise a DLT state, zeroing everything.
 * @return 0 on success, -1 if @p dlt is NULL.
 */
static inline int dlt_init(dlt_state_t *dlt)
{
    if (!dlt) return -1;
    memset(dlt, 0, sizeof(*dlt));
    return 0;
}

/**
 * Append a new layer with default thresholds.
 * @return layer index (0, 1, …) or -1 on failure.
 */
static inline int dlt_add_layer(dlt_state_t *dlt)
{
    if (!dlt || dlt->layer_count >= DLT_MAX_LAYERS) return -1;
    int idx = dlt->layer_count++;
    dlt_layer_t *l = &dlt->layers[idx];
    memset(l, 0, sizeof(*l));
    l->wp    = DLT_DEFAULT_WP;
    l->wn    = DLT_DEFAULT_WN;
    l->delta = DLT_DEFAULT_DELTA;
    return idx;
}

/**
 * Compute asymmetric deltas for a layer.
 *   delta_p = 0.7 × mean(|positive weights|)
 *   delta_n = 0.7 × mean(|negative weights|)
 * @return 0 on success, -1 if NULL.
 */
static inline int dlt_compute_asymmetric(dlt_state_t *dlt, int layer,
                                         const int weights[], int count)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return -1;
    dlt_layer_t *l = &dlt->layers[layer];

    long sum_pos = 0, n_pos = 0;
    long sum_neg = 0, n_neg = 0;
    for (int i = 0; i < count; i++) {
        if (weights[i] > 0) { sum_pos += dlt__abs(weights[i]); n_pos++; }
        else if (weights[i] < 0) { sum_neg += dlt__abs(weights[i]); n_neg++; }
    }

    l->delta_p = n_pos > 0 ? (int)(sum_pos * 7 / (n_pos * 10)) : 0;
    l->delta_n = n_neg > 0 ? (int)(sum_neg * 7 / (n_neg * 10)) : 0;
    return 0;
}

/**
 * Quantize weights into trits based on wp / wn boundaries.
 *   w > wp  →  +1
 *   w < wn  →  −1
 *   else    →   0
 * Updates count_pos, count_neg, count_zero, total_weights.
 * @return 0 on success, -1 on error.
 */
static inline int dlt_quantize(dlt_state_t *dlt, int layer,
                               const int weights[], trit out_trits[], int count)
{
    if (!dlt) return -1;
    if (layer < 0 || layer >= dlt->layer_count) return -1;
    dlt_layer_t *l = &dlt->layers[layer];

    l->count_pos = l->count_neg = l->count_zero = 0;
    l->total_weights = count;

    for (int i = 0; i < count; i++) {
        if (weights[i] > l->wp) {
            out_trits[i] = TRIT_TRUE;
            l->count_pos++;
        } else if (weights[i] < l->wn) {
            out_trits[i] = TRIT_FALSE;
            l->count_neg++;
        } else {
            out_trits[i] = TRIT_UNKNOWN;
            l->count_zero++;
        }
    }
    return 0;
}

/**
 * Count weights trapped in the deadzone:  0 < |w| < |wp| / 2.
 * @return number of trapped weights, or -1 on error.
 */
static inline int dlt_detect_trapped(dlt_state_t *dlt, int layer,
                                     const int weights[], int count)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return -1;
    dlt_layer_t *l = &dlt->layers[layer];

    int half = dlt__abs(l->wp) / 2;
    int trapped = 0;
    for (int i = 0; i < count; i++) {
        int aw = dlt__abs(weights[i]);
        if (aw > 0 && aw < half)
            trapped++;
    }
    l->trapped_count = trapped;
    return trapped;
}

/**
 * Trapping rate in permille [0, 1000].
 * @return rate, or 0 on bad layer.
 */
static inline int dlt_get_trapping_rate(const dlt_state_t *dlt, int layer)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return 0;
    const dlt_layer_t *l = &dlt->layers[layer];
    int tw = l->total_weights > 0 ? l->total_weights : 1;
    return l->trapped_count * 1000 / tw;
}

/**
 * Adjust wp / wn based on weight distribution.
 * wp stays ≥ 0, wn stays ≤ 0.
 * @return 0.
 */
static inline int dlt_update_thresholds(dlt_state_t *dlt, int layer,
                                        const int weights[], int count)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return -1;
    dlt_layer_t *l = &dlt->layers[layer];

    long sum_pos = 0, n_pos = 0;
    long sum_neg = 0, n_neg = 0;
    for (int i = 0; i < count; i++) {
        if (weights[i] > 0) { sum_pos += weights[i]; n_pos++; }
        else if (weights[i] < 0) { sum_neg += weights[i]; n_neg++; }
    }

    if (n_pos > 0) {
        int mean_pos = (int)(sum_pos / n_pos);
        l->wp = mean_pos > 0 ? mean_pos : 0;
    }
    if (n_neg > 0) {
        int mean_neg = (int)(sum_neg / n_neg);
        l->wn = mean_neg < 0 ? mean_neg : 0;
    }

    /* Ensure invariants */
    if (l->wp < 0) l->wp = 0;
    if (l->wn > 0) l->wn = 0;
    return 0;
}

/**
 * Straight-Through Estimator gradient accumulation.
 * For weights in the passthrough zone (|w| ≤ |wp|), accumulate gradients.
 * @return number of weights in passthrough zone, or 0 on error.
 */
static inline int dlt_ste_gradient(dlt_state_t *dlt, int layer,
                                   const int weights[], const int grads[],
                                   int count)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return 0;
    dlt_layer_t *l = &dlt->layers[layer];

    int awp = dlt__abs(l->wp);
    int passthrough = 0;
    for (int i = 0; i < count; i++) {
        if (dlt__abs(weights[i]) <= awp) {
            if (grads[i] > 0) l->grad_wp += grads[i];
            else if (grads[i] < 0) l->grad_wn += grads[i];
            passthrough++;
        }
    }
    return passthrough;
}

/**
 * Reactivate trapped weights by shrinking the dead-zone.
 * wp must not increase after reactivation.
 * @return number of freed weights, or -1 on error.
 */
static inline int dlt_reactivate(dlt_state_t *dlt, int layer,
                                 const int weights[], int count)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return -1;
    dlt_layer_t *l = &dlt->layers[layer];

    int old_wp = l->wp;

    /* Detect trapped before adjusting */
    int half = dlt__abs(l->wp) / 2;
    int trapped = 0;
    for (int i = 0; i < count; i++) {
        int aw = dlt__abs(weights[i]);
        if (aw > 0 && aw < half)
            trapped++;
    }

    /* Shrink dead-zone if trapping rate is significant */
    int tw = l->total_weights > 0 ? l->total_weights : count;
    int rate = trapped * 1000 / (tw > 0 ? tw : 1);
    if (rate > 50) {          /* >5 % trapping — shrink boundaries */
        l->wp = l->wp * 9 / 10;
        l->wn = l->wn * 9 / 10;
    } else if (trapped > 0) {
        l->wp = l->wp * 95 / 100;
        l->wn = l->wn * 95 / 100;
    }

    /* wp must not increase */
    if (l->wp > old_wp) l->wp = old_wp;

    /* Count freed weights under the new boundary */
    int new_half = dlt__abs(l->wp) / 2;
    int freed = 0;
    for (int i = 0; i < count; i++) {
        int aw = dlt__abs(weights[i]);
        if (aw > 0 && aw < half && aw >= new_half)
            freed++;
    }

    l->reactivated += freed;
    return freed;
}

/**
 * Sparsity in permille [0, 1000].
 * @return count_zero × 1000 / total_weights.
 */
static inline int dlt_get_sparsity(const dlt_state_t *dlt, int layer)
{
    if (!dlt || layer < 0 || layer >= dlt->layer_count) return 0;
    const dlt_layer_t *l = &dlt->layers[layer];
    int tw = l->total_weights > 0 ? l->total_weights : 1;
    return l->count_zero * 1000 / tw;
}

/**
 * Quantisation accuracy in permille.
 * Counts how many quantised trits match the sign of the original weight.
 * @return accuracy ∈ [0, 1000].
 */
static inline int dlt_quant_accuracy(const int weights[], const trit quant_trits[],
                                     int count)
{
    if (count <= 0) return 0;
    int match = 0;
    for (int i = 0; i < count; i++) {
        int sign_w = (weights[i] > 0) ? 1 : (weights[i] < 0) ? -1 : 0;
        if ((int)quant_trits[i] == sign_w)
            match++;
    }
    return match * 1000 / count;
}

#ifdef __cplusplus
}
#endif

#endif /* TRIT_DLT_H */
