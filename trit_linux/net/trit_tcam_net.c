/**
 * @file trit_tcam_net.c
 * @brief seT6 Ternary TCAM Network Search Module — implementation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_tcam_net.h"
#include <string.h>

/* ==== Internal helpers ================================================= */

/**
 * Check if a query matches an entry under its mask.
 * Returns TCAMN_MATCH_EXACT if all cared positions match exactly,
 * TCAMN_MATCH_WILDCARD if matched via Unknown/mask wildcard,
 * TCAMN_MATCH_NONE if mismatch.
 */
static int tcamn_entry_match(const tcamn_entry_t *entry, const trit *query) {
    int had_wildcard = 0;

    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) {
        /* If mask says "don't care", skip this position */
        if (entry->mask[i] != TRIT_TRUE) {
            had_wildcard = 1;
            continue;
        }
        /* If entry key is Unknown (wildcard) AND query differs, wildcard match */
        if (entry->key[i] == TRIT_UNKNOWN && query[i] != TRIT_UNKNOWN) {
            had_wildcard = 1;
            continue;
        }
        /* If query is Unknown AND entry key differs, partial match */
        if (query[i] == TRIT_UNKNOWN && entry->key[i] != TRIT_UNKNOWN) {
            had_wildcard = 1;
            continue;
        }
        /* Both same value (including both Unknown) → exact */
        if (entry->key[i] == query[i]) {
            continue;
        }
        /* Mismatch on a cared position */
        return TCAMN_MATCH_NONE;
    }

    return had_wildcard ? TCAMN_MATCH_WILDCARD : TCAMN_MATCH_EXACT;
}

/* ==== Public API ======================================================= */

int tcamn_init(tcamn_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int tcamn_add_entry(tcamn_state_t *st, const trit *key, const trit *mask,
                    int priority, tcamn_action_t action, int data) {
    if (!st || !st->initialized || !key) return -1;
    if (st->entry_count >= TCAMN_MAX_ENTRIES) return -1;

    int idx = st->entry_count;
    tcamn_entry_t *e = &st->entries[idx];
    memset(e, 0, sizeof(*e));

    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) {
        e->key[i] = key[i];
        e->mask[i] = mask ? mask[i] : TRIT_TRUE; /* Default: all care */
    }
    e->priority = priority;
    e->action = action;
    e->action_data = data;
    e->valid = 1;

    st->entry_count++;
    return idx;
}

int tcamn_search(tcamn_state_t *st, const trit *query, tcamn_result_t *result) {
    if (!st || !st->initialized || !query || !result) return -1;

    memset(result, 0, sizeof(*result));
    result->latency_ps = TCAMN_SEARCH_LATENCY_PS;

    st->total_searches++;
    st->total_energy_fj += TCAMN_ENERGY_PER_SEARCH_FJ;
    st->total_latency_ps += TCAMN_SEARCH_LATENCY_PS;

    /* Priority-ordered search: find best (lowest priority number) match */
    int best_idx = -1;
    int best_prio = 0x7FFFFFFF;
    int best_type = TCAMN_MATCH_NONE;

    for (int i = 0; i < st->entry_count; i++) {
        if (!st->entries[i].valid) continue;

        int mt = tcamn_entry_match(&st->entries[i], query);
        if (mt != TCAMN_MATCH_NONE) {
            if (st->entries[i].priority < best_prio) {
                best_prio = st->entries[i].priority;
                best_idx = i;
                best_type = mt;
            }
        }
    }

    if (best_idx >= 0) {
        result->matched = 1;
        result->entry_index = best_idx;
        result->match_type = best_type;
        result->action = st->entries[best_idx].action;
        result->action_data = st->entries[best_idx].action_data;
        result->trit_distance = tcamn_trit_distance(
            st->entries[best_idx].key, query, TCAMN_KEY_WIDTH);
        st->entries[best_idx].hit_count++;
        st->total_hits++;
        if (best_type == TCAMN_MATCH_EXACT)
            st->total_exact++;
        else
            st->total_wildcard++;
    } else {
        result->matched = 0;
        result->match_type = TCAMN_MATCH_NONE;
        st->total_misses++;
    }

    return 0;
}

int tcamn_trit_distance(const trit *a, const trit *b, int len) {
    if (!a || !b || len <= 0) return -1;

    int distance = 0;
    for (int i = 0; i < len; i++) {
        if (a[i] == TRIT_UNKNOWN || b[i] == TRIT_UNKNOWN) {
            /* Unknown contributes half distance (uncertain) */
            /* In integer: count as 0 (optimistic) */
            continue;
        }
        if (a[i] != b[i]) distance++;
    }
    return distance;
}

int tcamn_similarity_search(tcamn_state_t *st, const trit *query,
                            tcamn_result_t *results, int max_results) {
    if (!st || !st->initialized || !query || !results || max_results <= 0) return -1;

    /* Simple approach: compute distance to all entries, return sorted top-N */
    /* Using insertion sort since N is small */
    int found = 0;

    st->total_searches++;
    st->total_energy_fj += TCAMN_ENERGY_PER_SEARCH_FJ;
    st->total_latency_ps += TCAMN_SEARCH_LATENCY_PS;

    for (int i = 0; i < st->entry_count; i++) {
        if (!st->entries[i].valid) continue;

        int dist = tcamn_trit_distance(st->entries[i].key, query, TCAMN_KEY_WIDTH);

        /* Find insertion point (sorted by distance ascending) */
        int pos = found;
        for (int j = 0; j < found; j++) {
            if (dist < results[j].trit_distance) {
                pos = j;
                break;
            }
        }

        if (pos < max_results) {
            /* Shift entries down */
            int limit = (found < max_results) ? found : max_results - 1;
            for (int j = limit; j > pos; j--) {
                if (j < max_results)
                    results[j] = results[j - 1];
            }

            /* Insert */
            results[pos].matched = 1;
            results[pos].entry_index = i;
            results[pos].trit_distance = dist;
            results[pos].action = st->entries[i].action;
            results[pos].action_data = st->entries[i].action_data;
            results[pos].match_type = (dist == 0) ? TCAMN_MATCH_EXACT
                                                    : TCAMN_MATCH_WILDCARD;
            results[pos].latency_ps = TCAMN_SEARCH_LATENCY_PS;

            if (found < max_results) found++;
        }
    }

    return found;
}

int tcamn_delete_entry(tcamn_state_t *st, int index) {
    if (!st || !st->initialized) return -1;
    if (index < 0 || index >= st->entry_count) return -1;
    st->entries[index].valid = 0;
    return 0;
}

int tcamn_get_hit_rate(const tcamn_state_t *st) {
    if (!st || !st->initialized || st->total_searches == 0) return 0;
    return (st->total_hits * 100) / st->total_searches;
}

int64_t tcamn_get_energy(const tcamn_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->total_energy_fj;
}
