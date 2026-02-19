/**
 * @file trit_tcam_net.h
 * @brief seT6 Ternary TCAM Network Search Module
 *
 * AI-driven TCAM lookups inspired by Micron ReRAM TCAM architecture.
 * Ternary-native search with "don't care" as first-class Unknown state
 * (not a bitmask hack). Sub-nanosecond emulation for network routing,
 * firewall rules, and AI pattern matching.
 *
 * Key features:
 *   - Ternary match: exact/wildcard/masked using native trit logic
 *   - Priority-ordered rule evaluation (first match wins)
 *   - Sub-ns timing emulation (energy-aware)  
 *   - Pattern similarity scoring via Hamming/trit distance
 *   - Batch search for multi-pattern lookups
 *   - Statistics for hit rate, miss rate, power estimation
 *
 * @see hynix_tcam.h for existing crossbar TCAM integration
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_TCAM_NET_H
#define SET6_TRIT_TCAM_NET_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

#define TCAMN_MAX_ENTRIES     128   /**< Max TCAM table entries */
#define TCAMN_KEY_WIDTH       16    /**< Trits per key */
#define TCAMN_SEARCH_LATENCY_PS 800 /**< Emulated search latency (ps) */
#define TCAMN_ENERGY_PER_SEARCH_FJ 50 /**< Femtojoules per search */

/** Match result types */
#define TCAMN_MATCH_EXACT     2   /**< All trits match exactly */
#define TCAMN_MATCH_WILDCARD  1   /**< Matched via Unknown (wildcard) */
#define TCAMN_MATCH_NONE      0   /**< No match */

/** Action types (for firewall / routing) */
typedef enum {
    TCAMN_ACT_FORWARD,
    TCAMN_ACT_DROP,
    TCAMN_ACT_LOG,
    TCAMN_ACT_REDIRECT
} tcamn_action_t;

/* ==== Structures ======================================================= */

/**
 * @brief TCAM table entry.
 */
typedef struct {
    trit            key[TCAMN_KEY_WIDTH];    /**< Pattern (Unknown = wildcard) */
    trit            mask[TCAMN_KEY_WIDTH];   /**< TRUE=care, FALSE/UNK=ignore */
    int             priority;                /**< Lower = higher priority */
    tcamn_action_t  action;                  /**< Associated action */
    int             action_data;             /**< Action parameter (e.g., port) */
    int             hit_count;               /**< Times this entry matched */
    int             valid;                   /**< Entry is active */
} tcamn_entry_t;

/**
 * @brief Search result.
 */
typedef struct {
    int             matched;                 /**< 1 if found, 0 if miss */
    int             entry_index;             /**< Which entry matched */
    int             match_type;              /**< EXACT, WILDCARD, or NONE */
    int             trit_distance;           /**< Hamming distance to pattern */
    tcamn_action_t  action;                  /**< Action from matched entry */
    int             action_data;
    int             latency_ps;              /**< Emulated search time */
} tcamn_result_t;

/**
 * @brief TCAM net search engine state.
 */
typedef struct {
    int             initialized;

    /* Entry table */
    tcamn_entry_t   entries[TCAMN_MAX_ENTRIES];
    int             entry_count;

    /* Statistics */
    int             total_searches;
    int             total_hits;
    int             total_misses;
    int             total_exact;
    int             total_wildcard;
    int64_t         total_energy_fj;        /**< Cumulative energy */
    int64_t         total_latency_ps;       /**< Cumulative latency */
} tcamn_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize TCAM net engine.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int tcamn_init(tcamn_state_t *st);

/**
 * @brief Add a TCAM entry.
 * @param st        State.
 * @param key       Trit pattern.
 * @param mask      Care mask (TRUE=must match, else wildcard).
 * @param priority  Priority (lower = higher).
 * @param action    Action on match.
 * @param data      Action data.
 * @return Entry index, or -1 on error.
 */
int tcamn_add_entry(tcamn_state_t *st, const trit *key, const trit *mask,
                    int priority, tcamn_action_t action, int data);

/**
 * @brief Search TCAM for a key (first match by priority).
 * @param st     State.
 * @param query  Input key to match against entries.
 * @param result Output result.
 * @return 0 on success, -1 on error.
 */
int tcamn_search(tcamn_state_t *st, const trit *query, tcamn_result_t *result);

/**
 * @brief Compute trit Hamming distance between two keys.
 * @param a  First key.
 * @param b  Second key.
 * @param len Key length.
 * @return Number of differing positions (Unknown = 0.5 distance).
 */
int tcamn_trit_distance(const trit *a, const trit *b, int len);

/**
 * @brief Find top-N closest entries to a query (similarity search).
 * @param st       State.
 * @param query    Input key.
 * @param results  Array of results (caller allocated).
 * @param max_results  Max results to return.
 * @return Number of results found.
 */
int tcamn_similarity_search(tcamn_state_t *st, const trit *query,
                            tcamn_result_t *results, int max_results);

/**
 * @brief Delete an entry by index.
 * @param st     State.
 * @param index  Entry index.
 * @return 0 on success.
 */
int tcamn_delete_entry(tcamn_state_t *st, int index);

/**
 * @brief Get hit rate percentage.
 * @param st  State.
 * @return Hit rate (0-100).
 */
int tcamn_get_hit_rate(const tcamn_state_t *st);

/**
 * @brief Get total energy consumed (femtojoules).
 * @param st  State.
 * @return Total energy in fJ.
 */
int64_t tcamn_get_energy(const tcamn_state_t *st);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_TCAM_NET_H */
