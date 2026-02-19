/**
 * @file trit_chinchilla_opt.c
 * @brief seT6 Chinchilla-Optimal Ternary Training Scheduler — implementation.
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_chinchilla_opt.h"
#include <string.h>

/* ==== Integer Math Helpers ============================================== */

/** Integer natural log ×1000 (via log₂ and ln(2)). */
static int fp_ln(int x) {
    if (x <= 0) return 0;
    if (x == 1) return 0;
    int log2_int = 0, tmp = x;
    while (tmp > 1) { tmp >>= 1; log2_int++; }
    /* ln(x) = log₂(x) × ln(2), ln(2) ≈ 0.693 */
    int lo = 1 << log2_int;
    int hi = lo << 1;
    int frac = 0;
    if (hi > lo)
        frac = ((x - lo) * 1000) / (hi - lo);
    int log2_x1000 = log2_int * 1000 + frac;
    return (log2_x1000 * 693) / 1000;
}

/** Integer power: x^(a/1000) ×1000 via exp(a × ln(x) / 1000). */
static int fp_power(int x, int a_x1000) {
    if (x <= 0) return 0;
    if (a_x1000 == 0) return 1000;
    int ln_x = fp_ln(x);
    int exponent = (a_x1000 * ln_x) / 1000;
    /* exp(exponent/1000) ×1000 via Taylor: 1 + x + x²/2 + x³/6
     * Use int64_t intermediates to prevent overflow for large exponents. */
    int64_t e = exponent;
    int64_t e2 = (e * e) / (2 * 1000);
    int64_t e3 = (e * e / 1000 * e) / (6 * 1000);
    int64_t result = 1000 + e + e2 + e3;
    if (result < 0) result = 1;
    if (result > INT32_MAX) result = INT32_MAX;
    return (int)result;
}

/** Integer cosine approximation for LR scheduling.
 *  cos(π × t/T) ×1000, where t/T given as fraction ×1000.
 *  Uses quadratic approximation: cos(x) ≈ 1 - 2(x/π)² */
static int fp_cos(int frac_x1000) {
    /* frac maps [0, 1000] → [0, π],  cos(0)=1000, cos(π)=-1000 */
    /* Quadratic: cos ≈ 1000 - 2 × frac² / 1000 */
    int cos_val = 1000 - (2 * frac_x1000 * frac_x1000) / (1000 * 1000 / 1000);
    if (cos_val < -1000) cos_val = -1000;
    if (cos_val > 1000) cos_val = 1000;
    return cos_val;
}

/* ==== Scaling Laws ====================================================== */

/** Generic scaling law: L(N) = A / N^α + ε */
static int scaling_loss(int params_m, int A_x1000, int alpha_x1000, int eps_x1000) {
    if (params_m <= 0) return eps_x1000;
    int n_power = fp_power(params_m, alpha_x1000);
    if (n_power <= 0) n_power = 1;
    int term = (A_x1000 * 1000) / n_power;
    return term + eps_x1000;
}

/* ==== Public API ======================================================== */

int chi_init(chi_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int chi_trilm_loss(int params_m) {
    return scaling_loss(params_m, CHI_TRILM_A / 1000, CHI_TRILM_ALPHA, CHI_TRILM_EPS);
}

int chi_float_loss(int params_m) {
    return scaling_loss(params_m, CHI_FLOAT_A / 1000, CHI_FLOAT_ALPHA, CHI_FLOAT_EPS);
}

int chi_loss_gap(int params_m) {
    return chi_trilm_loss(params_m) - chi_float_loss(params_m);
}

int chi_build_schedule(chi_state_t *st, int params_m,
                       int peak_lr, int red_lr) {
    if (!st || !st->initialized || params_m <= 0 || peak_lr <= 0) return -1;

    /* Total steps = 300B tokens / (1M batch × 2048 seq_len) ≈ 146K steps
     * Simplified: total_steps = tokens_B × 1000 / batch_M / 2 */
    int total = (CHI_TOTAL_TOKENS_B * 1000) / (CHI_BATCH_TRILM * 2);
    int halfway = total / 2;
    int twothird = (total * 2) / 3;

    st->total_steps = total;
    st->phase_count = 0;

    /* Phase 1: Warmup + peak LR, weight decay on */
    st->schedule[0].start_step = 0;
    st->schedule[0].end_step = halfway;
    st->schedule[0].lr_x1e6 = peak_lr;
    st->schedule[0].weight_decay = 1;
    st->schedule[0].dlt_lr_x1e6 = peak_lr / 10;
    st->phase_count++;

    /* Phase 2: Reduced LR, weight decay still on */
    st->schedule[1].start_step = halfway;
    st->schedule[1].end_step = twothird;
    st->schedule[1].lr_x1e6 = red_lr;
    st->schedule[1].weight_decay = 1;
    st->schedule[1].dlt_lr_x1e6 = red_lr / 10;
    st->phase_count++;

    /* Phase 3: Reduced LR, no weight decay (ternarization regularizes) */
    st->schedule[2].start_step = twothird;
    st->schedule[2].end_step = total;
    st->schedule[2].lr_x1e6 = red_lr;
    st->schedule[2].weight_decay = 0;
    st->schedule[2].dlt_lr_x1e6 = red_lr / 10;
    st->phase_count++;

    return st->phase_count;
}

int chi_get_lr_at_step(const chi_state_t *st, int step) {
    if (!st || !st->initialized || st->phase_count == 0) return 0;

    /* Find which phase */
    int phase_lr = 0;
    int phase_start = 0, phase_end = 0;
    for (int i = 0; i < st->phase_count; i++) {
        if (step >= st->schedule[i].start_step &&
            step < st->schedule[i].end_step) {
            phase_lr = st->schedule[i].lr_x1e6;
            phase_start = st->schedule[i].start_step;
            phase_end = st->schedule[i].end_step;
            break;
        }
    }
    if (phase_lr == 0 && step >= st->total_steps)
        return CHI_LR_DECAY_FINAL;  /* End of training: minimum LR */

    /* Warmup for first 500 steps */
    if (step < CHI_WARMUP_STEPS) {
        return (phase_lr * step) / CHI_WARMUP_STEPS;
    }

    /* Cosine decay within phase */
    int phase_len = phase_end - phase_start;
    if (phase_len <= 0) return phase_lr;
    int progress = ((step - phase_start) * 1000) / phase_len;
    int cos_factor = fp_cos(progress);  /* [-1000, 1000] */
    /* LR = lr_min + 0.5 × (lr_max - lr_min) × (1 + cos(π × t/T)) */
    int lr_min = phase_lr / 10;  /* 10% of peak */
    int lr = lr_min + ((phase_lr - lr_min) * (1000 + cos_factor)) / 2000;
    if (lr < lr_min) lr = lr_min;
    return lr;
}

int chi_weight_decay_active(const chi_state_t *st, int step) {
    if (!st || !st->initialized) return 0;
    for (int i = 0; i < st->phase_count; i++) {
        if (step >= st->schedule[i].start_step &&
            step < st->schedule[i].end_step) {
            return st->schedule[i].weight_decay;
        }
    }
    return 0;
}

int chi_get_dlt_lr(const chi_state_t *st, int step) {
    int base_lr = chi_get_lr_at_step(st, step);
    return base_lr / 10;  /* DLT params at 0.1× */
}

int chi_populate_spectra(chi_state_t *st) {
    if (!st || !st->initialized) return -1;

    /* Spectra suite from Table 3 of TriLMs paper */
    static const struct {
        int params_m, hidden, glu, heads, layers, peak_lr, red_lr;
    } cfgs[] = {
        {  99,  512, 1280,  8, 16, 2400, 1500 },
        { 190,  768, 2048, 12, 16, 2400, 1500 },
        { 390, 1024, 2560, 16, 24, 1800, 1200 },
        { 560, 1280, 3072, 20, 24, 1600, 1100 },
        { 830, 1536, 4096, 24, 24, 1500, 1000 },
        {1100, 1792, 5120, 28, 24, 1300,  900 },
        {1500, 2048, 6144, 32, 24, 1200,  800 },
        {2400, 2304, 7680, 36, 30, 1200,  800 },
        {3900, 3072, 9216, 24, 30, 1200,  800 },
    };

    for (int i = 0; i < 9; i++) {
        st->spectra[i].params_m      = cfgs[i].params_m;
        st->spectra[i].hidden_dim    = cfgs[i].hidden;
        st->spectra[i].glu_dim       = cfgs[i].glu;
        st->spectra[i].heads         = cfgs[i].heads;
        st->spectra[i].layers        = cfgs[i].layers;
        st->spectra[i].peak_lr_x1e6  = cfgs[i].peak_lr;
        st->spectra[i].reduced_lr_x1e6 = cfgs[i].red_lr;
        st->spectra[i].estimated_loss = chi_trilm_loss(cfgs[i].params_m);
        st->spectra[i].gap_to_float   = chi_loss_gap(cfgs[i].params_m);
    }
    st->spectra_count = 9;
    return 0;
}

int chi_find_convergence(int threshold_x1000) {
    if (threshold_x1000 <= 0) return 0;
    /* Sweep from 100M to 10000M */
    for (int n = 100; n <= 10000; n += 50) {
        int gap = chi_loss_gap(n);
        if (gap <= threshold_x1000)
            return n;
    }
    return 0;  /* No convergence found */
}
