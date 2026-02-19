/**
 * @file godel_proof_searcher.c
 * @brief T-047: BIOPS-Inspired Proof Search Engine
 *
 * Enumerates candidate C modifications ranked by Kolmogorov complexity
 * proxy (shorter diffs first). Implements DGM's tiered evaluation pipeline:
 *
 *   Tier 1: gcc -fsyntax-only (compile check)
 *   Tier 2: isabelle build (proof gate — HARD REJECT)
 *   Tier 3: make test6 (unit tests)
 *   Tier 4: integration tests
 *   Tier 5: full benchmarks
 *
 * Each tier is a go/no-go gate. Failure at any tier rejects the candidate.
 * Favors modifications aligned with P(w) = 2^{-K(w)}.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* ── Configuration ── */
#define GPS_MAX_CANDIDATES  128
#define GPS_MAX_DIFF_LEN    4096
#define GPS_MAX_PATH_LEN    256
#define GPS_TIER_COUNT      5

/* ── Evaluation tiers ── */
typedef enum {
    GPS_TIER_COMPILE    = 0,  /* gcc -fsyntax-only */
    GPS_TIER_PROOF      = 1,  /* isabelle build */
    GPS_TIER_UNIT_TEST  = 2,  /* make test6 */
    GPS_TIER_INTEG_TEST = 3,  /* integration tests */
    GPS_TIER_BENCHMARK  = 4,  /* full benchmarks */
} gps_tier_t;

/* ── Candidate modification ── */
typedef struct {
    int     id;
    char    filepath[GPS_MAX_PATH_LEN];
    char    diff[GPS_MAX_DIFF_LEN];
    int     diff_len;               /* length as complexity proxy */
    double  kolmogorov_proxy;       /* 2^{-diff_len} */
    int     tier_results[GPS_TIER_COUNT]; /* 1=pass, 0=fail, -1=not_run */
    int     current_tier;
    int     rejected;
    int     accepted;
    double  utility_score;
    int     generation;
} gps_candidate_t;

/* ── Search state ── */
typedef struct {
    gps_candidate_t candidates[GPS_MAX_CANDIDATES];
    int             n_candidates;
    int             n_evaluated;
    int             n_accepted;
    int             n_rejected;
    int             budget_ms;      /* total evaluation budget */
    int             elapsed_ms;
    int             generation;
    int             initialized;
} gps_state_t;

/* ── API ── */

int gps_init(gps_state_t *st, int budget_ms) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->budget_ms = budget_ms;
    st->initialized = 1;
    return 0;
}

/**
 * @brief Add a candidate modification to the search queue.
 */
int gps_add_candidate(gps_state_t *st, const char *filepath,
                       const char *diff, int generation) {
    if (!st || !st->initialized) return -1;
    if (st->n_candidates >= GPS_MAX_CANDIDATES) return -1;
    if (!filepath || !diff) return -1;

    gps_candidate_t *c = &st->candidates[st->n_candidates];
    c->id = st->n_candidates;
    snprintf(c->filepath, sizeof(c->filepath), "%s", filepath);
    snprintf(c->diff, sizeof(c->diff), "%s", diff);
    c->diff_len = (int)strlen(diff);
    c->generation = generation;

    /* Kolmogorov complexity proxy: prefer shorter diffs */
    c->kolmogorov_proxy = 1.0;
    for (int i = 0; i < c->diff_len && i < 100; i++)
        c->kolmogorov_proxy *= 0.5; /* 2^{-len} */

    /* Initialize tier results */
    for (int t = 0; t < GPS_TIER_COUNT; t++)
        c->tier_results[t] = -1; /* not run */
    c->current_tier = 0;
    c->rejected = 0;
    c->accepted = 0;

    st->n_candidates++;
    return c->id;
}

/**
 * @brief Evaluate a candidate at its current tier.
 *
 * @param tier_passed 1 if the tier passed, 0 if failed
 * @return current tier index, or -1 if rejected/complete
 */
int gps_evaluate_tier(gps_state_t *st, int candidate_id, int tier_passed) {
    if (!st || !st->initialized) return -1;
    if (candidate_id < 0 || candidate_id >= st->n_candidates) return -1;

    gps_candidate_t *c = &st->candidates[candidate_id];
    if (c->rejected || c->accepted) return -1;

    /* Record tier result */
    c->tier_results[c->current_tier] = tier_passed ? 1 : 0;

    if (!tier_passed) {
        /* HARD REJECT at this tier */
        c->rejected = 1;
        st->n_rejected++;
        st->n_evaluated++;
        return -1;
    }

    c->current_tier++;

    /* All tiers passed? */
    if (c->current_tier >= GPS_TIER_COUNT) {
        c->accepted = 1;
        st->n_accepted++;
        st->n_evaluated++;
        return GPS_TIER_COUNT; /* complete */
    }

    return c->current_tier;
}

/**
 * @brief Get the next candidate to evaluate (lowest complexity first).
 *
 * @return candidate ID, or -1 if no candidates available
 */
int gps_next_candidate(const gps_state_t *st) {
    if (!st || !st->initialized) return -1;

    int best_id = -1;
    int best_len = GPS_MAX_DIFF_LEN + 1;

    for (int i = 0; i < st->n_candidates; i++) {
        const gps_candidate_t *c = &st->candidates[i];
        if (c->rejected || c->accepted) continue;
        if (c->diff_len < best_len) {
            best_len = c->diff_len;
            best_id = i;
        }
    }
    return best_id;
}

/**
 * @brief Get evaluation summary.
 */
typedef struct {
    int total_candidates;
    int evaluated;
    int accepted;
    int rejected;
    int pending;
    int tier_pass_rates[GPS_TIER_COUNT]; /* % pass per tier */
} gps_summary_t;

gps_summary_t gps_summary(const gps_state_t *st) {
    gps_summary_t s = {0};
    if (!st || !st->initialized) return s;

    s.total_candidates = st->n_candidates;
    s.evaluated = st->n_evaluated;
    s.accepted = st->n_accepted;
    s.rejected = st->n_rejected;
    s.pending = st->n_candidates - st->n_evaluated;

    /* Compute per-tier pass rates */
    int tier_tested[GPS_TIER_COUNT] = {0};
    int tier_passed[GPS_TIER_COUNT] = {0};
    for (int i = 0; i < st->n_candidates; i++) {
        for (int t = 0; t < GPS_TIER_COUNT; t++) {
            if (st->candidates[i].tier_results[t] >= 0) {
                tier_tested[t]++;
                if (st->candidates[i].tier_results[t] == 1)
                    tier_passed[t]++;
            }
        }
    }
    for (int t = 0; t < GPS_TIER_COUNT; t++) {
        s.tier_pass_rates[t] = (tier_tested[t] > 0) ?
            (tier_passed[t] * 100) / tier_tested[t] : 0;
    }
    return s;
}

/**
 * @brief Check if budget is exhausted.
 */
int gps_budget_exhausted(const gps_state_t *st) {
    if (!st || !st->initialized) return 1;
    return (st->elapsed_ms >= st->budget_ms) ? 1 : 0;
}
