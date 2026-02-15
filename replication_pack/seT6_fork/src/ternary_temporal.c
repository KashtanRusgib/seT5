/**
 * @file ternary_temporal.c
 * @brief seT6 Ternary Temporal Logic (TTL) — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/ternary_temporal.h"
#include <string.h>

/* ---- API -------------------------------------------------------------- */

void ttl_init(ttl_state_t *state) {
    memset(state, 0, sizeof(*state));
}

int ttl_register_prop(ttl_state_t *state, const char *name) {
    if (state->num_props >= TTL_MAX_PROPS)
        return -1;

    int id = state->num_props++;
    memset(&state->props[id], 0, sizeof(ttl_trace_t));

    /* Copy name safely */
    int i;
    for (i = 0; i < 31 && name[i]; i++)
        state->props[id].name[i] = name[i];
    state->props[id].name[i] = '\0';

    return id;
}

int ttl_observe(ttl_state_t *state, int prop_id, trit value) {
    if (prop_id < 0 || prop_id >= state->num_props)
        return -1;

    ttl_trace_t *trace = &state->props[prop_id];
    if (trace->length >= TTL_MAX_STEPS)
        return -1;

    trace->values[trace->length++] = value;
    return 0;
}

int ttl_advance(ttl_state_t *state) {
    state->current_step++;
    return state->current_step;
}

/* ---- Temporal Operators ----------------------------------------------- */

trit ttl_always(const ttl_state_t *state, int prop_id) {
    if (prop_id < 0 || prop_id >= state->num_props)
        return TRIT_UNKNOWN;

    const ttl_trace_t *trace = &state->props[prop_id];
    if (trace->length == 0)
        return TRIT_UNKNOWN;

    int has_unknown = 0;
    for (int i = 0; i < trace->length; i++) {
        if (trace->values[i] == TRIT_FALSE)
            return TRIT_FALSE;
        if (trace->values[i] == TRIT_UNKNOWN)
            has_unknown = 1;
    }

    return has_unknown ? TRIT_UNKNOWN : TRIT_TRUE;
}

trit ttl_eventually(const ttl_state_t *state, int prop_id) {
    if (prop_id < 0 || prop_id >= state->num_props)
        return TRIT_UNKNOWN;

    const ttl_trace_t *trace = &state->props[prop_id];
    if (trace->length == 0)
        return TRIT_UNKNOWN;

    int has_unknown = 0;
    for (int i = 0; i < trace->length; i++) {
        if (trace->values[i] == TRIT_TRUE)
            return TRIT_TRUE;
        if (trace->values[i] == TRIT_UNKNOWN)
            has_unknown = 1;
    }

    return has_unknown ? TRIT_UNKNOWN : TRIT_FALSE;
}

trit ttl_never(const ttl_state_t *state, int prop_id) {
    if (prop_id < 0 || prop_id >= state->num_props)
        return TRIT_UNKNOWN;

    const ttl_trace_t *trace = &state->props[prop_id];
    if (trace->length == 0)
        return TRIT_UNKNOWN;

    int has_unknown = 0;
    for (int i = 0; i < trace->length; i++) {
        if (trace->values[i] == TRIT_TRUE)
            return TRIT_FALSE;
        if (trace->values[i] == TRIT_UNKNOWN)
            has_unknown = 1;
    }

    return has_unknown ? TRIT_UNKNOWN : TRIT_TRUE;
}

trit ttl_until(const ttl_state_t *state, int prop_phi, int prop_psi) {
    if (prop_phi < 0 || prop_phi >= state->num_props ||
        prop_psi < 0 || prop_psi >= state->num_props)
        return TRIT_UNKNOWN;

    const ttl_trace_t *phi = &state->props[prop_phi];
    const ttl_trace_t *psi = &state->props[prop_psi];
    int len = (phi->length < psi->length) ? phi->length : psi->length;

    if (len == 0)
        return TRIT_UNKNOWN;

    for (int i = 0; i < len; i++) {
        /* If ψ is true at step i, φ held until now → TRUE */
        if (psi->values[i] == TRIT_TRUE)
            return TRIT_TRUE;

        /* If φ is false before ψ is true → FALSE */
        if (phi->values[i] == TRIT_FALSE)
            return TRIT_FALSE;
    }

    /* ψ never became true, φ never violated → UNKNOWN */
    return TRIT_UNKNOWN;
}

ttl_safety_t ttl_safety(const ttl_state_t *state, int prop_id) {
    if (prop_id < 0 || prop_id >= state->num_props)
        return TTL_UNCERTAIN;

    const ttl_trace_t *trace = &state->props[prop_id];
    if (trace->length == 0)
        return TTL_UNCERTAIN;

    int has_unknown = 0;
    for (int i = 0; i < trace->length; i++) {
        if (trace->values[i] == TRIT_FALSE)
            return TTL_VIOLATED;
        if (trace->values[i] == TRIT_UNKNOWN)
            has_unknown = 1;
    }

    return has_unknown ? TTL_UNCERTAIN : TTL_SAFE;
}

/* ---- Decision Logic --------------------------------------------------- */

ttl_decision_t ttl_decide(const ttl_state_t *state, int prop_id) {
    if (prop_id < 0 || prop_id >= state->num_props)
        return TTL_DECIDE_HOLD;

    const ttl_trace_t *trace = &state->props[prop_id];
    if (trace->length == 0)
        return TTL_DECIDE_HOLD;

    /* Look at recent observations (last 3 or all if shorter) */
    int window = trace->length < 3 ? trace->length : 3;
    int start  = trace->length - window;

    int trues = 0, falses = 0;
    for (int i = start; i < trace->length; i++) {
        if (trace->values[i] == TRIT_TRUE) trues++;
        if (trace->values[i] == TRIT_FALSE) falses++;
    }

    if (falses > 0)        return TTL_DECIDE_ABORT;
    if (trues == window)   return TTL_DECIDE_ACT;
    return TTL_DECIDE_HOLD;
}

void ttl_evaluate(ttl_result_t *result, const ttl_state_t *state, int prop_id) {
    memset(result, 0, sizeof(*result));

    if (prop_id < 0 || prop_id >= state->num_props) {
        result->value = TRIT_UNKNOWN;
        result->safety = TTL_UNCERTAIN;
        return;
    }

    const ttl_trace_t *trace = &state->props[prop_id];

    for (int i = 0; i < trace->length; i++) {
        switch (trace->values[i]) {
            case TRIT_TRUE:    result->true_count++;    break;
            case TRIT_FALSE:   result->false_count++;   break;
            default:           result->unknown_count++; break;
        }
    }

    /* Overall value: majority */
    if (result->true_count > result->false_count &&
        result->true_count > result->unknown_count)
        result->value = TRIT_TRUE;
    else if (result->false_count > result->true_count)
        result->value = TRIT_FALSE;
    else
        result->value = TRIT_UNKNOWN;

    result->safety = ttl_safety(state, prop_id);

    if (trace->length > 0)
        result->confidence_pct = ((result->true_count + result->false_count) * 100)
                                 / trace->length;
}

trit ttl_majority_vote(const ttl_state_t *state, const int *prop_ids, int count) {
    if (!prop_ids || count <= 0)
        return TRIT_UNKNOWN;

    int votes[3] = {0, 0, 0}; /* F, U, T */

    for (int i = 0; i < count; i++) {
        int id = prop_ids[i];
        if (id < 0 || id >= state->num_props) continue;

        const ttl_trace_t *trace = &state->props[id];
        if (trace->length == 0) {
            votes[1]++; /* UNKNOWN */
            continue;
        }

        /* Use most recent observation */
        trit latest = trace->values[trace->length - 1];
        switch (latest) {
            case TRIT_FALSE:   votes[0]++; break;
            case TRIT_UNKNOWN: votes[1]++; break;
            case TRIT_TRUE:    votes[2]++; break;
            default:           votes[1]++; break;
        }
    }

    if (votes[2] > votes[0] && votes[2] > votes[1])
        return TRIT_TRUE;
    if (votes[0] > votes[2] && votes[0] > votes[1])
        return TRIT_FALSE;
    return TRIT_UNKNOWN;
}

trit ttl_consensus(const ttl_state_t *state, const int *prop_ids, int count) {
    if (!prop_ids || count <= 0)
        return TRIT_UNKNOWN;

    int has_unknown = 0;
    for (int i = 0; i < count; i++) {
        int id = prop_ids[i];
        if (id < 0 || id >= state->num_props)
            return TRIT_UNKNOWN;

        const ttl_trace_t *trace = &state->props[id];
        if (trace->length == 0) {
            has_unknown = 1;
            continue;
        }

        trit latest = trace->values[trace->length - 1];
        if (latest == TRIT_FALSE)
            return TRIT_FALSE;
        if (latest == TRIT_UNKNOWN)
            has_unknown = 1;
    }

    return has_unknown ? TRIT_UNKNOWN : TRIT_TRUE;
}
