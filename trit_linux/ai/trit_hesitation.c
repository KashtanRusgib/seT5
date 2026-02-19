/**
 * @file trit_hesitation.c
 * @brief seT6 Epistemic Hesitation Reactor — Implementation
 *
 * Implements pause-on-Unknown decision engine with KL divergence,
 * B4 inconsistency detection, and confidence tracking.
 *
 * Key equations (sympy-verified):
 *   yield_B = exp(-D_KL(τ || q))
 *   D_KL(P || Q) = Σ P(x) × log(P(x) / Q(x))
 *   uncertainty = count_unknown / total
 *   hesitation trigger: uncertainty > 0.18
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_hesitation.h"
#include <string.h>

/* ==== Internal helpers ================================================== */

/**
 * @brief Fixed-point natural log approximation (×1000).
 * Uses 3rd-order Taylor around 1: ln(x) ≈ (x-1) - (x-1)²/2 + (x-1)³/3
 * Input x is in fixed-point ×1000, output is ln(x) ×1000.
 */
static int fp_ln(int x_fp)
{
    if (x_fp <= 0) return -7000; /* floor at ln(0.001) ≈ -7 */
    if (x_fp == 1000) return 0;

    /* For better range, use: ln(x) = ln(x/1000) in float-equivalent
     * We'll use a piecewise approach:
     *   ln(a/b) = ln(a) - ln(b)
     * For fixed-point, use iterative: ln(x) via repeated halving.
     *
     * Simple lookup table for common ratios: */
    /* ln(1/3)=-1099, ln(2/3)=-405, ln(1)=0, ln(4/3)=288, ln(5/3)=511 */

    /* Scale x to [500, 2000] range and track halvings */
    int shifts = 0;
    int xn = x_fp;
    while (xn > 2000) { xn = xn / 2; shifts++; }
    while (xn < 500 && xn > 0) { xn = xn * 2; shifts--; }

    /* Taylor series around 1 (x_fp=1000): d = (xn-1000)/1000 */
    long d = xn - 1000;
    /* ln(1+d) ≈ d - d²/2 + d³/3 (×1000) */
    long d2 = (d * d) / 1000;
    long d3 = (d2 * d) / 1000;
    int result = (int)(d - d2 / 2 + d3 / 3);

    /* Add back shifts: each *2 adds ln(2)=693 */
    result += shifts * 693;

    return result;
}

/**
 * @brief Fixed-point exp approximation (×1000).
 * Uses Taylor: exp(x) ≈ 1 + x + x²/2 + x³/6 + x⁴/24
 * Input x is in fixed-point ×1000, output is exp(x) ×1000.
 */
static int fp_exp(int x_fp)
{
    /* Clamp to reasonable range: exp(-7) ≈ 0.001, exp(2) ≈ 7.4 */
    if (x_fp < -7000) return 0;
    if (x_fp > 2000) return 7389;

    /* For negative values, use range reduction:
     * exp(x) = exp(x + k*ln2) / 2^k */
    long x = x_fp;
    /* Taylor: 1 + x + x²/2! + x³/3! + x⁴/4! (all ×1000) */
    long x2 = (x * x) / 1000;
    long x3 = (x2 * x) / 1000;
    long x4 = (x3 * x) / 1000;

    long result = 1000 + x + x2 / 2 + x3 / 6 + x4 / 24;

    if (result < 0) result = 0;
    if (result > 10000) result = 10000;

    return (int)result;
}

/**
 * @brief Recompute confidence metrics from rolling window.
 */
static void recompute_confidence(thes_channel_t *ch)
{
    int definite = 0, unknown = 0;
    int limit = ch->window_filled ? THES_WINDOW_SIZE :
                (ch->window_pos > 0 ? ch->window_pos : 1);

    for (int i = 0; i < limit; i++) {
        if (ch->window[i] == TRIT_UNKNOWN)
            unknown++;
        else
            definite++;
    }

    ch->conf.definiteness_pct = (definite * 100) / limit;
    ch->conf.unknown_rate_pct = (unknown * 100) / limit;
}

/**
 * @brief Convert distribution to fixed-point probabilities (×1000 each).
 */
static void dist_to_probs(const thes_distribution_t *d,
                           int *pf, int *pu, int *pt)
{
    int total = d->total > 0 ? d->total : 1;
    *pf = (int)(((int64_t)d->count_false  * 1000) / total);
    *pu = (int)(((int64_t)d->count_unknown * 1000) / total);
    *pt = (int)(((int64_t)d->count_true   * 1000) / total);

    /* Ensure no zero probs (Laplace smoothing effect) */
    if (*pf < THES_KL_EPSILON) *pf = THES_KL_EPSILON;
    if (*pu < THES_KL_EPSILON) *pu = THES_KL_EPSILON;
    if (*pt < THES_KL_EPSILON) *pt = THES_KL_EPSILON;
}

/* ==== Public API ======================================================== */

int thes_init(thes_reactor_t *reactor)
{
    if (!reactor) return -1;
    memset(reactor, 0, sizeof(*reactor));
    reactor->drift_threshold = THES_DRIFT_THRESHOLD;
    reactor->initialized = 1;
    return 0;
}

int thes_register_channel(thes_reactor_t *reactor)
{
    if (!reactor || !reactor->initialized) return -1;
    if (reactor->channel_count >= THES_MAX_CHANNELS) return -1;

    int id = reactor->channel_count++;
    thes_channel_t *ch = &reactor->channels[id];
    memset(ch, 0, sizeof(*ch));
    ch->active = 1;
    ch->state = THES_STATE_IDLE;
    ch->conf.last_definite = TRIT_UNKNOWN;
    return id;
}

int thes_observe(thes_reactor_t *reactor, int channel, trit value)
{
    if (!reactor || !reactor->initialized) return -1;
    if (channel < 0 || channel >= reactor->channel_count) return -1;

    thes_channel_t *ch = &reactor->channels[channel];
    if (!ch->active) return -1;

    /* Update rolling window */
    ch->window[ch->window_pos] = value;
    ch->window_pos = (ch->window_pos + 1) % THES_WINDOW_SIZE;
    if (ch->window_pos == 0) ch->window_filled = 1;

    /* Update distribution */
    ch->dist.total++;
    if (value == TRIT_FALSE) ch->dist.count_false++;
    else if (value == TRIT_UNKNOWN) ch->dist.count_unknown++;
    else if (value == TRIT_TRUE) ch->dist.count_true++;

    /* Track consecutive Unknowns */
    if (value == TRIT_UNKNOWN) {
        ch->conf.streak_unknown++;
        if (ch->conf.streak_unknown > ch->conf.max_streak_unknown)
            ch->conf.max_streak_unknown = ch->conf.streak_unknown;
    } else {
        ch->conf.streak_unknown = 0;
        ch->conf.last_definite = value;
    }

    /* Recompute confidence */
    recompute_confidence(ch);

    /* State transitions */
    int uncertainty = (int)(((int64_t)ch->dist.count_unknown * 100) / ch->dist.total);

    if (uncertainty > reactor->drift_threshold) {
        /* Uncertainty > 0.18 → hesitate */
        if (ch->state != THES_STATE_HESITATING) {
            ch->state = THES_STATE_HESITATING;
            ch->pauses++;
            reactor->total_pauses++;
        }
    } else {
        if (ch->state == THES_STATE_HESITATING ||
            ch->state == THES_STATE_IDLE) {
            ch->state = THES_STATE_RUNNING;
        }
        ch->decisions++;
        reactor->total_decisions++;
    }

    /* Check B4 inconsistency */
    if (thes_b4_check(&ch->dist)) {
        reactor->total_b4_flags++;
    }

    return ch->state;
}

int thes_get_confidence(const thes_reactor_t *reactor, int channel,
                        thes_confidence_t *out)
{
    if (!reactor || !reactor->initialized) return -1;
    if (channel < 0 || channel >= reactor->channel_count) return -1;
    if (!out) return -1;

    *out = reactor->channels[channel].conf;
    return 0;
}

int thes_kl_divergence(const thes_distribution_t *p,
                       const thes_distribution_t *q)
{
    if (!p || !q) return -1;

    int pf, pu, pt, qf, qu, qt;
    dist_to_probs(p, &pf, &pu, &pt);
    dist_to_probs(q, &qf, &qu, &qt);

    /* D_KL(P||Q) = Σ P(x) × ln(P(x)/Q(x)) */
    /* All in fixed-point ×1000 */
    int kl = 0;

    /* For each trit value: p_i * ln(p_i / q_i) */
    /* p_i/q_i in fixed-point: (p_i * 1000) / q_i */
    if (pf > THES_KL_EPSILON) {
        int ratio = (pf * 1000) / qf;
        kl += (pf * fp_ln(ratio)) / 1000;
    }
    if (pu > THES_KL_EPSILON) {
        int ratio = (pu * 1000) / qu;
        kl += (pu * fp_ln(ratio)) / 1000;
    }
    if (pt > THES_KL_EPSILON) {
        int ratio = (pt * 1000) / qt;
        kl += (pt * fp_ln(ratio)) / 1000;
    }

    /* KL divergence is always non-negative */
    if (kl < 0) kl = 0;

    return kl;
}

int thes_yield(const thes_distribution_t *tau,
               const thes_distribution_t *q)
{
    int kl = thes_kl_divergence(tau, q);
    if (kl < 0) return -1;

    /* yield_B = exp(-D_KL(τ, q)) */
    return fp_exp(-kl);
}

int thes_b4_check(const thes_distribution_t *dist)
{
    if (!dist) return 0;

    /* B4 "Both" = has significant TRUE and FALSE simultaneously.
     * In Belnap four-valued logic:
     *   T = only true, F = only false, B = both, N = neither
     * We detect "Both" when both true and false counts exceed
     * a threshold relative to total observations. */
    if (dist->total < 2) return 0;

    int true_pct  = (dist->count_true  * 100) / dist->total;
    int false_pct = (dist->count_false * 100) / dist->total;

    /* B4 inconsistency: both truth values present significantly
     * (each > 15% of observations) */
    if (true_pct > 15 && false_pct > 15)
        return 1;

    return 0;
}

int thes_recalibrate(thes_reactor_t *reactor, int channel)
{
    if (!reactor || !reactor->initialized) return -1;
    if (channel < 0 || channel >= reactor->channel_count) return -1;

    thes_channel_t *ch = &reactor->channels[channel];
    memset(&ch->dist, 0, sizeof(ch->dist));
    memset(&ch->conf, 0, sizeof(ch->conf));
    memset(ch->window, 0, sizeof(ch->window));
    ch->window_pos = 0;
    ch->window_filled = 0;
    ch->state = THES_STATE_RECAL;
    ch->recalibrations++;
    return 0;
}

int thes_get_drift(const thes_reactor_t *reactor)
{
    if (!reactor || !reactor->initialized) return 0;
    if (reactor->channel_count == 0) return 0;

    int total_unknown_pct = 0;
    int active_count = 0;

    for (int i = 0; i < reactor->channel_count; i++) {
        const thes_channel_t *ch = &reactor->channels[i];
        if (!ch->active || ch->dist.total == 0) continue;
        total_unknown_pct += (int)(((int64_t)ch->dist.count_unknown * 100) / ch->dist.total);
        active_count++;
    }

    if (active_count == 0) return 0;
    return total_unknown_pct / active_count;
}

int thes_get_total_pauses(const thes_reactor_t *reactor)
{
    if (!reactor) return 0;
    return reactor->total_pauses;
}

int thes_get_total_decisions(const thes_reactor_t *reactor)
{
    if (!reactor) return 0;
    return reactor->total_decisions;
}

int thes_dlt_react(thes_reactor_t *reactor, int channel,
                   int trapping_rate, int target_rate)
{
    if (!reactor || !reactor->initialized) return -1;
    if (channel < 0 || channel >= reactor->channel_count) return -1;

    thes_channel_t *ch = &reactor->channels[channel];
    if (!ch->active || ch->dist.total == 0) return -1;

    /* Compute channel's Unknown rate ×1000 */
    int unknown_rate = (int)(((int64_t)ch->dist.count_unknown * 1000)
                             / ch->dist.total);

    /* DLT reactivation recommended if:
     *   1. Channel Unknown rate > drift_threshold (×10 to convert ×100→×1000)
     *   2. DLT trapping rate > target */
    int thresh_x1000 = reactor->drift_threshold * 10;  /* 18 → 180 */

    if (unknown_rate > thresh_x1000 && trapping_rate > target_rate)
        return 1;

    return 0;
}
