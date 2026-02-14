/**
 * @file ternary_temporal.h
 * @brief seT5 Ternary Temporal Logic (TTL) — Uncertainty Semantics
 *
 * 3-valued temporal logic for epistemic uncertainty in safety-critical
 * systems. Unlike binary logic that forces hallucinated decisions,
 * TTL uses the third state to represent "genuinely unknown" conditions.
 *
 * Logic values:
 *   TRUE    (+1) — Condition verified
 *   UNKNOWN ( 0) — Insufficient evidence (epistemic uncertainty)
 *   FALSE   (-1) — Condition refuted
 *
 * Temporal operators:
 *   ALWAYS(φ)   — φ holds at all observed time steps
 *   EVENTUALLY(φ) — φ holds at some future time step
 *   UNTIL(φ,ψ)  — φ holds until ψ becomes true
 *   SAFETY(φ)   — φ has never been false (unknown is acceptable)
 *
 * Applications:
 *   - Autonomous vehicle decision logic (uncertain sensor fusion)
 *   - AI safety guards (prevent binary hallucination)
 *   - Ternary model checking / verification
 *   - EW (electronic warfare) contested-environment reasoning
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Uncertainty-Injected 3-Valued Semantics
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_TERNARY_TEMPORAL_H
#define SET5_TERNARY_TEMPORAL_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Maximum observable time steps in a trace */
#define TTL_MAX_STEPS       256

/** Maximum propositions tracked simultaneously */
#define TTL_MAX_PROPS       16

/** Decision outcomes */
typedef enum {
    TTL_DECIDE_ACT,          /**< Sufficient evidence to act */
    TTL_DECIDE_HOLD,         /**< Uncertain — hold/defer action */
    TTL_DECIDE_ABORT         /**< Condition refuted — abort */
} ttl_decision_t;

/** Safety levels */
typedef enum {
    TTL_SAFE,                /**< No false observations */
    TTL_UNCERTAIN,           /**< Has unknowns, no false */
    TTL_VIOLATED             /**< Safety violated (false observed) */
} ttl_safety_t;

/* ==== Structures ======================================================= */

/**
 * @brief Temporal trace of a single proposition.
 */
typedef struct {
    trit   values[TTL_MAX_STEPS]; /**< Trit value at each time step */
    int    length;                 /**< Number of recorded steps */
    char   name[32];               /**< Proposition identifier */
} ttl_trace_t;

/**
 * @brief Multi-proposition temporal state.
 */
typedef struct {
    ttl_trace_t  props[TTL_MAX_PROPS]; /**< Proposition traces */
    int          num_props;             /**< Active propositions */
    int          current_step;          /**< Current time step */
} ttl_state_t;

/**
 * @brief Temporal evaluation result.
 */
typedef struct {
    trit         value;          /**< Evaluated truth value */
    ttl_safety_t safety;         /**< Safety assessment */
    int          confidence_pct; /**< Confidence (0-100) */
    int          true_count;     /**< Time steps with TRUE */
    int          unknown_count;  /**< Time steps with UNKNOWN */
    int          false_count;    /**< Time steps with FALSE */
} ttl_result_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize temporal logic state.
 */
void ttl_init(ttl_state_t *state);

/**
 * @brief Register a named proposition.
 * @param state  TTL state.
 * @param name   Proposition name (max 31 chars).
 * @return       Proposition index, or -1 if full.
 */
int ttl_register_prop(ttl_state_t *state, const char *name);

/**
 * @brief Record a trit observation for a proposition at current step.
 * @param state   TTL state.
 * @param prop_id Proposition index.
 * @param value   Observed trit value.
 * @return        0 on success, -1 on error.
 */
int ttl_observe(ttl_state_t *state, int prop_id, trit value);

/**
 * @brief Advance to next time step.
 * @param state  TTL state.
 * @return       New time step index.
 */
int ttl_advance(ttl_state_t *state);

/* ---- Temporal Operators ----------------------------------------------- */

/**
 * @brief ALWAYS(φ): Has φ been true at every observed step?
 *
 * Returns TRUE if all steps are TRUE.
 * Returns UNKNOWN if any step is UNKNOWN (but none FALSE).
 * Returns FALSE if any step is FALSE.
 */
trit ttl_always(const ttl_state_t *state, int prop_id);

/**
 * @brief EVENTUALLY(φ): Has φ been true at any observed step?
 *
 * Returns TRUE if any step is TRUE.
 * Returns UNKNOWN if no TRUE but some UNKNOWN.
 * Returns FALSE if all steps are FALSE.
 */
trit ttl_eventually(const ttl_state_t *state, int prop_id);

/**
 * @brief NEVER(φ): Has φ never been true?
 *
 * Returns TRUE if no step is TRUE.
 * Returns UNKNOWN if no TRUE but some UNKNOWN.
 * Returns FALSE if any step is TRUE.
 */
trit ttl_never(const ttl_state_t *state, int prop_id);

/**
 * @brief UNTIL(φ, ψ): φ holds until ψ becomes true.
 *
 * Returns TRUE if ψ eventually true and φ holds until then.
 * Returns UNKNOWN if ψ never observed but φ not violated.
 * Returns FALSE if φ violated before ψ.
 */
trit ttl_until(const ttl_state_t *state, int prop_phi, int prop_psi);

/**
 * @brief SAFETY(φ): φ has never been false.
 *
 * Weaker than ALWAYS — unknowns are acceptable.
 * Returns SAFE if no FALSE, UNCERTAIN if unknowns present, VIOLATED otherwise.
 */
ttl_safety_t ttl_safety(const ttl_state_t *state, int prop_id);

/* ---- Decision Logic --------------------------------------------------- */

/**
 * @brief Make a ternary-aware decision based on proposition state.
 *
 * ACT if sufficient recent TRUEs, HOLD if uncertain, ABORT if FALSE.
 *
 * @param state   TTL state.
 * @param prop_id Proposition to decide on.
 * @return        Decision outcome.
 */
ttl_decision_t ttl_decide(const ttl_state_t *state, int prop_id);

/**
 * @brief Evaluate with full result details.
 */
void ttl_evaluate(ttl_result_t *result, const ttl_state_t *state, int prop_id);

/**
 * @brief Ternary majority vote across multiple propositions.
 *
 * Returns the majority trit value. Ties broken toward UNKNOWN.
 *
 * @param state    TTL state.
 * @param prop_ids Array of proposition indices.
 * @param count    Number of propositions.
 * @return         Majority trit value.
 */
trit ttl_majority_vote(const ttl_state_t *state, const int *prop_ids, int count);

/**
 * @brief Consensus across propositions at current step.
 *
 * Returns TRUE only if ALL props are TRUE.
 * Returns FALSE if ANY prop is FALSE.
 * Returns UNKNOWN otherwise.
 */
trit ttl_consensus(const ttl_state_t *state, const int *prop_ids, int count);

#ifdef __cplusplus
}
#endif

#endif /* SET5_TERNARY_TEMPORAL_H */
