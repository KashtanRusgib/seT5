/**
 * @file ternary_weight_quantizer.c
 * @brief seT6 Ternary Weight Quantizer (TWQ) — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/ternary_weight_quantizer.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

/** Simple abs for int32_t */
static int32_t i32_abs(int32_t v) { return v < 0 ? -v : v; }

/** xorshift32 PRNG for stochastic mode */
static uint32_t twq_xorshift(uint32_t *seed) {
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/* ---- API Implementation ----------------------------------------------- */

void twq_config_init(twq_config_t *cfg) {
    cfg->mode      = TWQ_MODE_SYMMETRIC;
    cfg->delta_num = TWQ_DEFAULT_DELTA_FACTOR_NUM;
    cfg->delta_den = TWQ_DEFAULT_DELTA_FACTOR_DEN;
    cfg->wp_scale  = 1000;
    cfg->wn_scale  = 1000;
    cfg->rng_seed  = 42;
}

int twq_quantize(twq_layer_t *layer, const int32_t *weights, int count,
                 const twq_config_t *cfg) {
    if (!layer || !weights || count <= 0 || count > TWQ_MAX_WEIGHTS)
        return -1;

    memset(layer, 0, sizeof(*layer));
    layer->count  = count;
    layer->config = *cfg;

    /* Compute mean absolute weight */
    int64_t sum_abs = 0;
    for (int i = 0; i < count; i++)
        sum_abs += i32_abs(weights[i]);
    int32_t mean_abs = (int32_t)(sum_abs / count);

    /* Compute threshold: Δ = factor × mean|w| */
    int32_t delta = (mean_abs * cfg->delta_num) / cfg->delta_den;
    if (delta <= 0) delta = 1;

    /* Quantize */
    uint32_t rng = cfg->rng_seed;
    int pos = 0, neg = 0, zero = 0;

    for (int i = 0; i < count; i++) {
        int32_t w = weights[i];
        trit q;

        if (cfg->mode == TWQ_MODE_STOCHASTIC) {
            /* Probabilistic rounding near threshold */
            int32_t abs_w = i32_abs(w);
            if (abs_w > delta) {
                q = (w > 0) ? TRIT_TRUE : TRIT_FALSE;
            } else {
                /* Probability proportional to |w|/Δ */
                uint32_t r = twq_xorshift(&rng) % (uint32_t)(delta + 1);
                if ((int32_t)r < abs_w) {
                    q = (w > 0) ? TRIT_TRUE : TRIT_FALSE;
                } else {
                    q = TRIT_UNKNOWN;
                }
            }
        } else {
            /* Deterministic thresholding */
            if (w > delta)       q = TRIT_TRUE;
            else if (w < -delta) q = TRIT_FALSE;
            else                 q = TRIT_UNKNOWN;
        }

        layer->weights[i] = q;
        if (q == TRIT_TRUE)     pos++;
        else if (q == TRIT_FALSE) neg++;
        else                    zero++;
    }

    /* Fill statistics */
    layer->stats.total_weights   = count;
    layer->stats.positive_count  = pos;
    layer->stats.zero_count      = zero;
    layer->stats.negative_count  = neg;
    layer->stats.sparsity_permille = (zero * 1000) / count;
    layer->stats.mean_abs_x1000  = (int)(mean_abs);
    layer->stats.threshold_x1000 = (int)(delta);
    layer->stats.mac_savings_pct = (zero * 100) / count;

    return 0;
}

int twq_ternary_dot(const trit *a, const trit *b, int len) {
    int acc = 0;
    for (int i = 0; i < len; i++)
        acc += (int)a[i] * (int)b[i];
    return acc;
}

int twq_matvec_row(const trit *weights, const trit *input, int in_features) {
    int acc = 0;
    for (int i = 0; i < in_features; i++) {
        trit w = weights[i];
        if (w == TRIT_UNKNOWN) continue;     /* skip (zero weight) */
        if (w == TRIT_TRUE)    acc += input[i];  /* add */
        else                   acc -= input[i];  /* subtract */
    }
    return acc;
}

int twq_enforce_sparsity(twq_layer_t *layer, int n, int m) {
    if (!layer || n <= 0 || m <= 0 || m >= n)
        return -1;

    int zeroed = 0;
    for (int i = 0; i < layer->count; i += n) {
        int block_end = i + n;
        if (block_end > layer->count) block_end = layer->count;
        int block_len = block_end - i;

        /* Count non-zeros in block */
        int nonzero = 0;
        for (int j = i; j < block_end; j++)
            if (layer->weights[j] != TRIT_UNKNOWN) nonzero++;

        /* If too many non-zeros, zero out excess (keep first M) */
        if (nonzero > m) {
            int kept = 0;
            for (int j = i; j < block_end; j++) {
                if (layer->weights[j] != TRIT_UNKNOWN) {
                    kept++;
                    if (kept > m) {
                        layer->weights[j] = TRIT_UNKNOWN;
                        zeroed++;
                    }
                }
            }
        }
        (void)block_len;
    }

    /* Update stats */
    int zero = 0;
    for (int i = 0; i < layer->count; i++)
        if (layer->weights[i] == TRIT_UNKNOWN) zero++;
    layer->stats.zero_count = zero;
    layer->stats.sparsity_permille = (zero * 1000) / layer->count;
    layer->stats.mac_savings_pct = (zero * 100) / layer->count;

    return zeroed;
}

int twq_energy_ratio(const twq_stats_t *stats) {
    if (!stats || stats->total_weights == 0) return 0;

    /* FP16 MAC ~= 15500 fJ, Ternary add ~= 900 fJ */
    /* Base ratio: 900/15500 ≈ 58/1000 */
    int base_ratio = 58;

    /* Sparsity savings: zero-skip trits cost nothing */
    int effective = 1000 - stats->sparsity_permille;
    return (base_ratio * effective) / 1000;
}

int twq_dequantize(int32_t *out, const twq_layer_t *layer) {
    if (!out || !layer) return -1;

    for (int i = 0; i < layer->count; i++) {
        trit w = layer->weights[i];
        if (w == TRIT_TRUE)
            out[i] = layer->config.wp_scale;
        else if (w == TRIT_FALSE)
            out[i] = -(int32_t)layer->config.wn_scale;
        else
            out[i] = 0;
    }
    return layer->count;
}
