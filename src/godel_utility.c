/**
 * @file godel_utility.c
 * @brief T-046: Gödel Machine Utility Metric Calculator
 *
 * Implements the Sigma 9 composite score as the Gödel machine's
 * reward function r(τ). Tracks delta utility per modification.
 *
 * u(s,Env) = (tests_passing/tests_total)
 *          × (proofs_verified/proofs_total)
 *          × (trit_functions/total_functions)
 *          × (1 - binary_reversion_count/total_functions)
 *
 * Self-improvement criterion: accept IFF Δu > c(proof)/norm_const
 *
 * Implements DGM-style CMP (Cumulative Marginal Potential) from HGM.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* ── Configuration ── */
#define GUTIL_MAX_HISTORY     256
#define GUTIL_NORMALIZATION   1000.0  /* cost normalization constant */

/* ── Component scores ── */
typedef struct {
    double u_tests;        /* tests_passing / tests_total */
    double u_proofs;       /* proofs_verified / proofs_total */
    double u_trit;         /* trit_functions / total_functions */
    double u_revert;       /* 1 - binary_reversions / total_functions */
    double u_composite;    /* product of all components */
} gutil_score_t;

/* ── Cost accounting ── */
typedef struct {
    int    build_time_ms;
    int    test_time_ms;
    int    isabelle_time_ms;
    int    total_time_ms;
    double normalized_cost;
} gutil_cost_t;

/* ── History entry ── */
typedef struct {
    int           generation;
    gutil_score_t score;
    gutil_cost_t  cost;
    double        delta_u;
    trit          accepted;       /* +1=accepted, 0=deferred, -1=rejected */
    char          patch_id[64];
} gutil_history_t;

/* ── CMP (Cumulative Marginal Potential) ── */
typedef struct {
    double marginal_gain;    /* sum of delta_u for all accepted patches */
    double marginal_cost;    /* sum of normalized_cost for accepted patches */
    double cmp;              /* marginal_gain / marginal_cost */
    int    total_candidates;
    int    total_accepted;
    int    total_rejected;
} gutil_cmp_t;

/* ── State ── */
typedef struct {
    gutil_score_t    current;
    gutil_score_t    previous;
    gutil_cost_t     last_cost;
    gutil_history_t  history[GUTIL_MAX_HISTORY];
    int              n_history;
    gutil_cmp_t      cmp;
    trit             initialized;  /* +1=ready, 0=partial, -1=uninit */
} gutil_state_t;

/* ── API ── */

int gutil_init(gutil_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = TRIT_TRUE;
    return 0;
}

/**
 * @brief Compute composite utility score.
 */
gutil_score_t gutil_compute(int tests_pass, int tests_total,
                             int proofs_ok, int proofs_total,
                             int trit_funcs, int total_funcs,
                             int binary_reverts) {
    gutil_score_t s;
    s.u_tests  = (tests_total > 0) ? (double)tests_pass / tests_total : 0.0;
    s.u_proofs = (proofs_total > 0) ? (double)proofs_ok / proofs_total : 0.0;
    s.u_trit   = (total_funcs > 0) ? (double)trit_funcs / total_funcs : 0.0;
    s.u_revert = (total_funcs > 0) ?
        1.0 - (double)binary_reverts / total_funcs : 1.0;
    s.u_composite = s.u_tests * s.u_proofs * s.u_trit * s.u_revert;
    return s;
}

/**
 * @brief Compute cost of a modification.
 */
gutil_cost_t gutil_cost(int build_ms, int test_ms, int isabelle_ms) {
    gutil_cost_t c;
    c.build_time_ms    = build_ms;
    c.test_time_ms     = test_ms;
    c.isabelle_time_ms = isabelle_ms;
    c.total_time_ms    = build_ms + test_ms + isabelle_ms;
    c.normalized_cost  = (double)c.total_time_ms / GUTIL_NORMALIZATION;
    return c;
}

/**
 * @brief Evaluate whether a modification should be accepted.
 *
 * Self-improvement criterion: Δu > cost / normalization
 *
 * @return +1 (TRIT_TRUE) if accepted, 0 (TRIT_UNKNOWN) if marginal, -1 (TRIT_FALSE) if rejected
 */
trit gutil_evaluate(gutil_state_t *st, gutil_score_t new_score,
                    gutil_cost_t cost, const char *patch_id) {
    if (!st || st->initialized != TRIT_TRUE) return TRIT_FALSE;

    st->previous = st->current;
    double delta_u = new_score.u_composite - st->current.u_composite;

    /* Ternary decision: accept / defer / reject */
    trit accepted;
    if (delta_u > cost.normalized_cost)
        accepted = TRIT_TRUE;       /* clear improvement */
    else if (delta_u >= 0)
        accepted = TRIT_UNKNOWN;    /* marginal — defer for more evidence */
    else
        accepted = TRIT_FALSE;      /* regression — reject */

    /* Record history */
    if (st->n_history < GUTIL_MAX_HISTORY) {
        gutil_history_t *h = &st->history[st->n_history];
        h->generation = st->n_history;
        h->score = new_score;
        h->cost = cost;
        h->delta_u = delta_u;
        h->accepted = accepted;
        if (patch_id)
            snprintf(h->patch_id, sizeof(h->patch_id), "%s", patch_id);
        st->n_history++;
    }

    /* Update CMP */
    st->cmp.total_candidates++;
    if (accepted == TRIT_TRUE) {
        st->current = new_score;
        st->last_cost = cost;
        st->cmp.total_accepted++;
        st->cmp.marginal_gain += delta_u;
        st->cmp.marginal_cost += cost.normalized_cost;
        if (st->cmp.marginal_cost > 0)
            st->cmp.cmp = st->cmp.marginal_gain / st->cmp.marginal_cost;
    } else {
        st->cmp.total_rejected++;
    }

    return accepted;
}

/**
 * @brief Get delta utility for the last evaluation.
 */
double gutil_delta_u(const gutil_state_t *st) {
    if (!st || st->initialized != TRIT_TRUE || st->n_history == 0) return 0.0;
    return st->history[st->n_history - 1].delta_u;
}

/**
 * @brief Get the CMP (Cumulative Marginal Potential).
 */
gutil_cmp_t gutil_get_cmp(const gutil_state_t *st) {
    if (!st || st->initialized != TRIT_TRUE) {
        gutil_cmp_t zero = {0};
        return zero;
    }
    return st->cmp;
}

/**
 * @brief Check if utility decomposition holds:
 *        u = u_tests × u_proofs × u_trit × u_revert
 */
int gutil_verify_decomposition(const gutil_score_t *s) {
    if (!s) return 0;
    double expected = s->u_tests * s->u_proofs * s->u_trit * s->u_revert;
    double diff = s->u_composite - expected;
    return (diff < 1e-10 && diff > -1e-10) ? 1 : 0;
}

/**
 * @brief Check transitivity: if u(s1) > u(s0) and u(s2) > u(s1),
 *        then u(s2) > u(s0).
 */
int gutil_verify_transitivity(double u0, double u1, double u2) {
    if (u1 > u0 && u2 > u1)
        return (u2 > u0) ? 1 : 0;
    return 1; /* precondition not met, vacuously true */
}
