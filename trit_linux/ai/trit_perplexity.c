/**
 * @file trit_perplexity.c
 * @brief seT6 Perplexity Benchmark Engine — Implementation
 *
 * Integer-only PPL estimation using Taylor-series exp() and log().
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_perplexity.h"
#include <string.h>

/* ---- helpers ----------------------------------------------------------- */

/** Integer absolute value. */
static int32_t abs_val(int32_t x) { return x < 0 ? -x : x; }

/**
 * Integer exp(x/1000) × 1000 — uses 4th-order Taylor.
 * Good for x/1000 in [0, 4.0] which covers PPL up to ~55.
 *   e^x ≈ 1 + x + x²/2 + x³/6 + x⁴/24
 */
static int32_t fp_exp(int32_t x_x1000)
{
    if (x_x1000 <= 0) return 1000;       /* e^0 = 1.0 */
    if (x_x1000 > 4000) {
        /* Use e^4 ≈ 54.598, then scale linearly for safety */
        return 54598;
    }

    int64_t x  = (int64_t)x_x1000;
    int64_t x2 = x * x / 1000;
    int64_t x3 = x2 * x / 1000;
    int64_t x4 = x3 * x / 1000;

    int64_t result = 1000 + x + x2 / 2 + x3 / 6 + x4 / 24;
    if (result > 100000000LL) result = 100000000LL; /* clamp */
    return (int32_t)result;
}

/**
 * Integer ln(x/1000) × 1000 — for x > 0.
 * Uses iterative approach: find n where e^n ≈ x.
 */
static int32_t fp_ln(int32_t x_x1000)
{
    if (x_x1000 <= 0) return -10000;
    if (x_x1000 == 1000) return 0;

    /* Binary search for ln: find y such that exp(y) = x */
    int32_t lo = -3000, hi = 12000;
    for (int i = 0; i < 30; i++) {
        int32_t mid = (lo + hi) / 2;
        int32_t est = fp_exp(mid);
        if (est < x_x1000) lo = mid;
        else                hi = mid;
    }
    return (lo + hi) / 2;
}

/* ---- API implementation ------------------------------------------------ */

int ppl_init(ppl_state_t *st)
{
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    for (int d = 0; d < PPL_NUM_DATASETS; d++) {
        st->best_ternary_ppl[d] = -1;
        st->best_float_ppl[d]   = -1;
    }
    return 0;
}

int ppl_add_model(ppl_state_t *st, int model_type, int32_t params_m,
                  int32_t loss_x1000)
{
    if (!st || !st->initialized) return -1;
    if (st->model_count >= PPL_MAX_MODELS) return -1;
    if (model_type < 0 || model_type >= PPL_NUM_MODEL_TYPES) return -1;

    int idx = st->model_count++;
    ppl_model_config_t *m = &st->models[idx];
    memset(m, 0, sizeof(*m));
    m->model_type = model_type;
    m->params_m   = params_m;
    m->loss_x1000 = loss_x1000;
    m->has_ref    = 0;
    return idx;
}

int ppl_set_reference(ppl_state_t *st, int model_idx, int dataset,
                      int32_t ppl_x1000)
{
    if (!st || !st->initialized) return -1;
    if (model_idx < 0 || model_idx >= st->model_count) return -1;
    if (dataset < 0 || dataset >= PPL_NUM_DATASETS) return -1;

    st->models[model_idx].ref_ppl[dataset] = ppl_x1000;
    st->models[model_idx].has_ref = 1;
    return 0;
}

int32_t ppl_from_cross_entropy(int32_t cross_entropy_x1000)
{
    /* PPL = exp(CE) */
    return fp_exp(cross_entropy_x1000);
}

int32_t ppl_ce_from_bpw(int32_t bpw_x1000)
{
    /* CE = H(W) × ln(2) */
    return (int32_t)((int64_t)bpw_x1000 * PPL_LN2_X1000 / 1000);
}

int ppl_evaluate(ppl_state_t *st, int model_idx, int dataset,
                 ppl_result_t *out)
{
    if (!st || !st->initialized || !out) return -1;
    if (model_idx < 0 || model_idx >= st->model_count) return -1;
    if (dataset < 0 || dataset >= PPL_NUM_DATASETS) return -1;

    ppl_model_config_t *m = &st->models[model_idx];
    memset(out, 0, sizeof(*out));
    out->dataset_id = dataset;
    out->model_type = m->model_type;

    if (m->has_ref && m->ref_ppl[dataset] > 0) {
        /* Use published reference value */
        out->ppl_x1000 = m->ref_ppl[dataset];
        /* Back-compute cross-entropy: CE = ln(PPL) */
        out->cross_entropy_x1000 = fp_ln(out->ppl_x1000);
    } else {
        /* Estimate from training loss (CE ≈ loss for LM) */
        out->cross_entropy_x1000 = m->loss_x1000;
        out->ppl_x1000 = fp_exp(m->loss_x1000);
    }

    /* Bits per word: H = CE / ln(2) */
    if (PPL_LN2_X1000 > 0) {
        out->bits_per_word_x1000 = (int32_t)(
            (int64_t)out->cross_entropy_x1000 * 1000 / PPL_LN2_X1000);
    }

    /* Compute gap to FP16 baseline */
    int32_t fp16_ref = 0;
    switch (dataset) {
        case PPL_DATASET_WIKITEXT2: fp16_ref = PPL_REF_FP16_WIKI; break;
        case PPL_DATASET_C4:        fp16_ref = PPL_REF_FP16_C4;   break;
        case PPL_DATASET_PTB:       fp16_ref = PPL_REF_FP16_PTB;  break;
        case PPL_DATASET_LAMBADA:   fp16_ref = PPL_REF_FLOAT_LAMBADA; break;
    }
    out->gap_to_fp16_x1000 = out->ppl_x1000 - fp16_ref;

    /* Store result */
    if (st->result_count < PPL_MAX_MODELS * PPL_NUM_DATASETS) {
        st->results[st->result_count++] = *out;
    }

    /* Track best per dataset */
    if (m->model_type == PPL_MODEL_TRILM_NATIVE ||
        m->model_type == PPL_MODEL_TERNARY_DLT  ||
        m->model_type == PPL_MODEL_TERNARY_OFF) {
        if (st->best_ternary_ppl[dataset] < 0 ||
            out->ppl_x1000 < st->best_ternary_ppl[dataset]) {
            st->best_ternary_ppl[dataset] = out->ppl_x1000;
        }
    }
    if (m->model_type == PPL_MODEL_FP16) {
        if (st->best_float_ppl[dataset] < 0 ||
            out->ppl_x1000 < st->best_float_ppl[dataset]) {
            st->best_float_ppl[dataset] = out->ppl_x1000;
        }
    }

    return 0;
}

int32_t ppl_degradation_ratio(int32_t ternary_ppl_x1000,
                               int32_t fp16_ppl_x1000)
{
    if (fp16_ppl_x1000 <= 0) return -1;
    return (int32_t)((int64_t)ternary_ppl_x1000 * 1000 / fp16_ppl_x1000);
}

int ppl_gap_acceptable(int32_t gap_x1000)
{
    return (gap_x1000 <= PPL_ACCEPTABLE_GAP) ? 1 : 0;
}

int ppl_ternary_beats_float(int32_t ternary_ppl_x1000,
                             int32_t float_ppl_x1000)
{
    return (ternary_ppl_x1000 <= float_ppl_x1000) ? 1 : 0;
}

int32_t ppl_best_ternary(ppl_state_t *st, int dataset)
{
    if (!st || !st->initialized) return -1;
    if (dataset < 0 || dataset >= PPL_NUM_DATASETS) return -1;
    return st->best_ternary_ppl[dataset];
}
