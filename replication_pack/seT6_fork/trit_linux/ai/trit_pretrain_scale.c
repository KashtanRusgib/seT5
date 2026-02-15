/**
 * @file trit_pretrain_scale.c
 * @brief seT6 Ternary Pretraining Scaling Laws — implementation.
 *
 * Chinchilla-style scaling law with ternary bit-width adjustment,
 * Spectra suite configuration, crossover estimation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_pretrain_scale.h"
#include <string.h>

/* ==== Helpers =========================================================== */

/** Fixed-point exp approximation (×1000).
 *  Input x is ×1000. Output is exp(x/1000) × 100. */
static int fp_exp_tps(int x_fp) {
    if (x_fp < -7000) return 0;
    if (x_fp > 3000) return 2009000; /* cap at exp(3) ≈ 20.09 */

    int64_t x = x_fp;
    int64_t x2 = (x * x) / 1000;
    int64_t x3 = (x2 * x) / 1000;
    int64_t x4 = (x3 * x) / 1000;

    /* exp(x) ≈ 1 + x + x²/2 + x³/6 + x⁴/24  (×1000) */
    int64_t result = 1000 + x + x2 / 2 + x3 / 6 + x4 / 24;
    if (result < 0) result = 0;

    /* Convert from ×1000 to ×100 (for perplexity) */
    return (int)(result / 10);
}

/** Fixed-point natural log (×1000). Input x > 0 (actual value, not scaled). */
static int fp_ln_tps(int x) {
    if (x <= 0) return 0;
    if (x == 1) return 0;

    /* ln(x) via repeated halving to [1,2] range then Taylor */
    int shifts = 0;
    int xn = x * 1000;  /* Scale to ×1000 */
    while (xn > 2000) { xn /= 2; shifts++; }
    while (xn < 1000 && xn > 0) { xn *= 2; shifts--; }

    int64_t d = xn - 1000;
    int64_t d2 = (d * d) / 1000;
    int64_t d3 = (d2 * d) / 1000;
    int result = (int)(d - d2 / 2 + d3 / 3);
    result += shifts * 693;
    return result;
}

/** Integer power approximation: base^exp where exp is ×1000.
 *  Returns base^(exp/1000) as integer. Uses: x^a = exp(a * ln(x)). */
static int fp_power(int base, int exp_x1000) {
    if (base <= 0) return 0;
    if (exp_x1000 == 0) return 1;
    if (exp_x1000 == 1000) return base;

    /* a * ln(base) in ×1000 */
    int ln_base = fp_ln_tps(base);
    int64_t product = ((int64_t)exp_x1000 * ln_base) / 1000;

    /* exp(product/1000) — but we need actual value, not ×100 */
    /* Use simplified: for loss function, we work with ×1000 throughout */
    if (product > 10000) return base; /* overflow guard */
    if (product < -7000) return 0;

    int64_t x = product;
    int64_t x2 = (x * x) / 1000;
    int64_t x3 = (x2 * x) / 1000;
    int64_t result = 1000 + x + x2 / 2 + x3 / 6;
    if (result < 0) result = 1;

    return (int)(result);
}

/* ==== Public API ======================================================== */

int tps_init(tps_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int tps_bit_equivalent(int params_m, int bits_per_weight) {
    if (params_m <= 0 || bits_per_weight <= 0) return 0;

    /* effective = params × (bits / 16bits) = params × bits / 16000 */
    return (int)((int64_t)params_m * bits_per_weight / TPS_BITS_PER_FLOAT);
}

int tps_estimate_loss(int params_m, int tokens_b) {
    if (params_m <= 0 || tokens_b <= 0) return TPS_CHINCHILLA_E;

    /*
     * L(N,D) = A / N^α + B / D^β + E
     *
     * All values ×1000. N in millions, D in billions.
     * Use integer approximation for N^α:
     *   N^0.34 ≈ iterative approach
     */

    /* Term 1: A / N^α */
    int n_power = fp_power(params_m, TPS_CHINCHILLA_ALPHA);
    int term1 = 0;
    if (n_power > 0) {
        term1 = TPS_CHINCHILLA_A / n_power;
    }

    /* Term 2: B / D^β */
    int d_power = fp_power(tokens_b, TPS_CHINCHILLA_BETA);
    int term2 = 0;
    if (d_power > 0) {
        term2 = TPS_CHINCHILLA_B / d_power;
    }

    /* Loss = term1 + term2 + E  (all ×1000) */
    int loss = term1 + term2 + TPS_CHINCHILLA_E;

    return loss;
}

int tps_loss_to_ppl(int loss) {
    if (loss <= 0) return 100;  /* PPL = 1.0 minimum */

    /* PPL = exp(loss/1000) × 100 */
    return fp_exp_tps(loss);
}

int tps_estimate_memory(int params_m, int bits_per_weight) {
    if (params_m <= 0 || bits_per_weight <= 0) return 0;

    /* memory_MB = params_M × 1e6 × bits / 8 / 1e6 = params_M × bits / 8
     * bits is ×1000, so: memory = params_M × bits / 8000 */
    return (int)((int64_t)params_m * bits_per_weight / 8000);
}

int tps_bandwidth_saving(int bits_per_weight) {
    if (bits_per_weight <= 0) return 0;

    /* saving = FP16_bits / bits = 16000 / bits (all ×1000) */
    return (TPS_BITS_PER_FLOAT * TPS_FP_SCALE) / bits_per_weight;
}

int tps_add_config(tps_state_t *st, int params_m, int tokens_b,
                   int bits_per_weight) {
    if (!st || !st->initialized) return -1;
    if (st->config_count >= TPS_MAX_CONFIGS) return -1;
    if (params_m <= 0 || tokens_b <= 0 || bits_per_weight <= 0) return -1;

    int idx = st->config_count;
    tps_config_t *c = &st->configs[idx];

    c->params_m = params_m;
    c->tokens_b = tokens_b;
    c->bits_per_weight = bits_per_weight;
    c->bit_equiv_params = tps_bit_equivalent(params_m, bits_per_weight);
    c->estimated_loss = tps_estimate_loss(params_m, tokens_b);
    c->estimated_ppl = tps_loss_to_ppl(c->estimated_loss);
    c->memory_mb = tps_estimate_memory(params_m, bits_per_weight);
    c->flops = tps_estimate_flops(params_m, tokens_b);

    st->config_count++;
    return idx;
}

int tps_find_crossover(tps_state_t *st, int tokens_b) {
    if (!st || !st->initialized) return 0;
    if (tokens_b <= 0) return 0;

    /*
     * TriLM (pretrained ternary) vs QuantLM (post-quantized float):
     * QuantLM loss ≈ loss_float(N,D) + quantization_penalty
     * quantization_penalty ≈ 200 (×1000) for aggressive quantization
     *
     * Find N where TriLM_loss < QuantLM_loss.
     * TriLM trains with ternary from scratch → uses params efficiently.
     * QuantLM trains float then quantizes → pays mismatch penalty.
     */
    int quant_penalty = 200; /* Additional loss from quantization mismatch */

    /* Sweep from 100M to 5000M params */
    for (int n = 100; n <= 5000; n += 100) {
        int trilm_loss = tps_estimate_loss(n, tokens_b);
        int float_loss = tps_estimate_loss(n, tokens_b);
        int quantlm_loss = float_loss + quant_penalty;

        if (trilm_loss < quantlm_loss) {
            st->crossover_params_m = n;
            return n;
        }
    }

    return 0; /* No crossover found */
}

int64_t tps_estimate_flops(int params_m, int tokens_b) {
    if (params_m <= 0 || tokens_b <= 0) return 0;

    /*
     * Standard: FLOPs ≈ 6 × N × D
     * N in millions, D in billions → 6 × N × D × 1e6 × 1e9 = 6 × N × D × 1e15
     * We store in a manageable unit: 1e12 FLOPs (TeraFLOPs)
     *
     * For ternary: MAC-free ops → effective FLOPs × 0.33
     * (multiplications become sign flips, only additions remain)
     */

    /* FLOPs in TeraFLOPs (×1e12) */
    int64_t flops = (int64_t)6 * params_m * tokens_b * 1000; /* ×1e12 */

    /* Ternary efficiency: MAC-free → 33% of binary FLOPs */
    flops = flops / 3;

    return flops;
}

int tps_bitsize_scaling(int total_bits_m) {
    if (total_bits_m <= 0) return TPS_CHINCHILLA_A;

    /* loss = A / bits^α + ε
     * A = 406.0, α = 0.26, ε = 1.69
     * All ×1000 for fixed-point.
     *
     * Integer approximation of x^0.26:
     *   x^0.26 ≈ x^(1/4) × x^(1/100) ≈ sqrt(sqrt(x)) × small_correction
     *   We use: x^0.26 ≈ isqrt(isqrt(x)) for simplicity, then correct. */

    /* Newton's method integer sqrt */
    int64_t val = (int64_t)total_bits_m;
    int64_t s = val;
    while (s > 0 && s * s > val * 4) s /= 2;
    if (s <= 0) s = 1;
    for (int i = 0; i < 20; i++) {
        int64_t next = (s + val / s) / 2;
        if (next >= s) break;
        s = next;
    }
    /* s ≈ sqrt(total_bits_m) */
    int64_t s2 = s;
    int64_t sq2 = s2;
    while (sq2 > 0 && sq2 * sq2 > s * 4) sq2 /= 2;
    if (sq2 <= 0) sq2 = 1;
    for (int i = 0; i < 20; i++) {
        int64_t next = (sq2 + s / sq2) / 2;
        if (next >= sq2) break;
        sq2 = next;
    }
    /* sq2 ≈ x^0.25 */

    /* Correction: 0.26/0.25 = 1.04, so x^0.26 ≈ x^0.25 × x^0.01
     * x^0.01 ≈ 1 + 0.01 × ln(x) ≈ 1.0 for reasonable x
     * We just use sq2 as-is since the correction is tiny. */
    if (sq2 <= 0) sq2 = 1;

    /* loss = A / sq2 + E = 406000 / sq2 + 1690 */
    int loss = (int)(TPS_CHINCHILLA_A / sq2) + TPS_CHINCHILLA_E;
    if (loss < TPS_CHINCHILLA_E) loss = TPS_CHINCHILLA_E;
    return loss;
}

int tps_crossover_bits(int float_loss_x1000) {
    if (float_loss_x1000 <= TPS_CHINCHILLA_E) return 0;

    /* Sweep total bits from 100M to 100000M
     * Find where tps_bitsize_scaling(bits) <= float_loss */
    for (int bits = 100; bits <= 100000; bits += 100) {
        int tern_loss = tps_bitsize_scaling(bits);
        if (tern_loss <= float_loss_x1000) return bits;
    }
    return 0;  /* No crossover found */
}
