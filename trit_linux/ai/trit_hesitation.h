/**
 * @file trit_hesitation.h
 * @brief seT6 Epistemic Hesitation Reactor — Pause-on-Unknown Decision Engine
 *
 * Implements epistemic uncertainty handling for ternary AI pipelines:
 *   - Hesitation Reactor: pauses processing when K3 Unknown exceeds threshold
 *   - KL-Divergence estimation between trit distributions (τ vs q)
 *   - Yield function: B = exp(-D_KL(τ, q)) for epistemic resonance
 *   - B4 inconsistency detection (four-valued extension guard)
 *   - Confidence tracking with rolling window
 *   - Drift monitoring: triggers recalibration when uncertainty > 0.18
 *
 * Theory: In Kleene K3, Unknown (0) represents genuine epistemic
 * uncertainty — not a neutral value. The hesitation reactor treats
 * it as a signal to pause and gather more information, rather than
 * making a potentially wrong binary decision.
 *
 * Reference: 2026 epistemic uncertainty models (K3/B4 equations),
 * sympy-verified resonance formulas.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_HESITATION_H
#define SET6_TRIT_HESITATION_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define THES_MAX_PIPELINE      64     /* Max pipeline depth                 */
#define THES_WINDOW_SIZE       32     /* Confidence rolling window          */
#define THES_DRIFT_THRESHOLD   18     /* 0.18 in fixed-point (×100)        */
#define THES_B4_BOTH_FLAG      2      /* B4: "Both" truth value indicator   */
#define THES_YIELD_SCALE       1000   /* Fixed-point scale for yield values */
#define THES_MAX_CHANNELS      8      /* Max monitored channels             */
#define THES_KL_EPSILON        1      /* Avoid log(0) — maps to 1/SCALE    */

/* Reactor states */
#define THES_STATE_IDLE        0
#define THES_STATE_RUNNING     1
#define THES_STATE_HESITATING  2      /* Paused on Unknown                  */
#define THES_STATE_DIVERGED    3      /* KL-div exceeded threshold          */
#define THES_STATE_RECAL       4      /* Recalibrating                      */

/* ==== Types ============================================================= */

/**
 * @brief Trit distribution — frequencies of {-1, 0, +1}.
 * Used for KL divergence and confidence estimation.
 */
typedef struct {
    int count_false;                   /**< Count of TRIT_FALSE             */
    int count_unknown;                 /**< Count of TRIT_UNKNOWN           */
    int count_true;                    /**< Count of TRIT_TRUE              */
    int total;                         /**< Total observations              */
} thes_distribution_t;

/**
 * @brief Confidence metric for a trit channel.
 */
typedef struct {
    int   definiteness_pct;            /**< % of definite trits in window   */
    int   unknown_rate_pct;            /**< % of Unknown trits in window    */
    int   streak_unknown;              /**< Consecutive Unknowns current    */
    int   max_streak_unknown;          /**< Peak consecutive Unknowns       */
    trit  last_definite;               /**< Last definite value seen        */
} thes_confidence_t;

/**
 * @brief Hesitation channel — one monitored decision stream.
 */
typedef struct {
    int   active;                      /**< Channel is being monitored      */
    int   state;                       /**< THES_STATE_*                    */
    thes_distribution_t dist;          /**< Running distribution            */
    thes_confidence_t   conf;          /**< Confidence metrics              */
    trit  window[THES_WINDOW_SIZE];    /**< Rolling observation window      */
    int   window_pos;                  /**< Next write position in window   */
    int   window_filled;               /**< Window has been fully filled    */
    int   pauses;                      /**< Total hesitation pauses         */
    int   decisions;                   /**< Total decisions made            */
    int   recalibrations;              /**< Times recalibrated              */
} thes_channel_t;

/**
 * @brief Hesitation reactor engine state.
 */
typedef struct {
    int             initialized;
    thes_channel_t  channels[THES_MAX_CHANNELS];
    int             channel_count;
    int             total_pauses;       /**< Global pause count             */
    int             total_decisions;    /**< Global decision count          */
    int             total_divergences;  /**< KL-div threshold breaches      */
    int             total_b4_flags;     /**< B4 inconsistency detections    */
    int             drift_threshold;    /**< In fixed-point (×100)          */
} thes_reactor_t;

/* ==== API =============================================================== */

/** Initialize the hesitation reactor. */
int thes_init(thes_reactor_t *reactor);

/** Register a new channel for monitoring. Returns channel ID or -1. */
int thes_register_channel(thes_reactor_t *reactor);

/** Feed a trit observation to a channel. Returns new channel state. */
int thes_observe(thes_reactor_t *reactor, int channel, trit value);

/** Get confidence metrics for a channel. */
int thes_get_confidence(const thes_reactor_t *reactor, int channel,
                        thes_confidence_t *out);

/** Compute KL divergence D_KL(P || Q) in fixed-point (×1000).
 *  P = channel distribution, Q = reference (e.g., uniform). */
int thes_kl_divergence(const thes_distribution_t *p,
                       const thes_distribution_t *q);

/** Compute yield B = exp(-D_KL(τ, q)) in fixed-point (×1000).
 *  Returns [0, 1000] where 1000 = perfect alignment. */
int thes_yield(const thes_distribution_t *tau,
               const thes_distribution_t *q);

/** Check B4 inconsistency: both TRUE and FALSE seen for same context.
 *  Returns 1 if inconsistent (B4 "Both" detected), 0 otherwise. */
int thes_b4_check(const thes_distribution_t *dist);

/** Force recalibration: reset channel distribution and confidence. */
int thes_recalibrate(thes_reactor_t *reactor, int channel);

/** Get global drift level across all channels (fixed-point ×100). */
int thes_get_drift(const thes_reactor_t *reactor);

/** Get total hesitation pauses across all channels. */
int thes_get_total_pauses(const thes_reactor_t *reactor);

/** Get total decisions made across all channels. */
int thes_get_total_decisions(const thes_reactor_t *reactor);

/**
 * @brief DLT-trapping reactor: detect if deadzone trapping is causing
 *        excessive Unknown observations.
 *
 * If a channel's Unknown rate exceeds the threshold AND the external
 * DLT trapping_rate is above target, this function flags the channel
 * for DLT reactivation.
 *
 * @param reactor        Hesitation reactor.
 * @param channel        Channel index.
 * @param trapping_rate  DLT trapping rate ×1000 (from dlt_get_trapping_rate).
 * @param target_rate    Target maximum trapping rate ×1000.
 * @return 1 if DLT reactivation recommended, 0 if not, -1 on error.
 */
int thes_dlt_react(thes_reactor_t *reactor, int channel,
                   int trapping_rate, int target_rate);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_HESITATION_H */
