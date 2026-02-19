/**
 * @file godel_archive.c
 * @brief T-055: Gödel Machine Variant Archive Manager
 *
 * Tracks lineage of seT6 variants. Maps to DGM's evo_utils.py.
 *
 * API:
 *   - archive_store()         — persist variant with metadata
 *   - archive_select_parent() — choose parent by selection method
 *   - archive_get_lineage()   — ordered ancestor chain
 *   - archive_get_fitness()   — multi-objective fitness vector
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* ── Configuration ── */
#define ARCHIVE_MAX_VARIANTS   512
#define ARCHIVE_MAX_ID_LEN     64
#define ARCHIVE_MAX_DIFF_PATH  256

/* ── Selection methods ── */
typedef enum {
    ARCHIVE_SELECT_RANDOM         = 0,
    ARCHIVE_SELECT_SCORE_PROP     = 1,  /* score-proportional */
    ARCHIVE_SELECT_SCORE_CHILD    = 2,  /* score × 1/(1+children) */
    ARCHIVE_SELECT_BEST           = 3,
} archive_select_t;

/* ── Multi-objective fitness vector ── */
typedef struct {
    int     compiles;           /* 1/0 */
    int     proofs_pass;        /* count of verified proofs */
    int     tests_pass;         /* count of passing tests */
    double  trit_coverage;      /* % of functions that are trit-native */
    int     benchmark_ns;       /* benchmark time in nanoseconds */
    double  utility;            /* composite Sigma 9 score */
} archive_fitness_t;

/* ── Variant entry ── */
typedef struct {
    char              variant_id[ARCHIVE_MAX_ID_LEN];
    char              parent_id[ARCHIVE_MAX_ID_LEN];
    char              diff_path[ARCHIVE_MAX_DIFF_PATH];
    archive_fitness_t fitness;
    int               generation;
    int               children;     /* number of mutations derived from this */
    int               active;       /* 1 if still in archive */
    uint32_t          timestamp;    /* creation time (epoch seconds) */
} archive_entry_t;

/* ── Archive state ── */
typedef struct {
    archive_entry_t  entries[ARCHIVE_MAX_VARIANTS];
    int              n_entries;
    int              best_idx;
    double           best_utility;
    uint32_t         rng_seed;
    int              initialized;
} archive_state_t;

/* ── Simple PRNG ── */
static uint32_t arch_rng(uint32_t *seed) {
    uint32_t x = *seed;
    x ^= x << 13; x ^= x >> 17; x ^= x << 5;
    *seed = x;
    return x;
}

/* ── API ── */

int archive_init(archive_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->rng_seed = 42;
    st->best_idx = -1;
    st->initialized = 1;
    return 0;
}

/**
 * @brief Store a new variant in the archive.
 */
int archive_store(archive_state_t *st, const char *variant_id,
                   const char *parent_id, const archive_fitness_t *fitness,
                   int generation, const char *diff_path) {
    if (!st || !st->initialized || !variant_id) return -1;
    if (st->n_entries >= ARCHIVE_MAX_VARIANTS) return -1;

    archive_entry_t *e = &st->entries[st->n_entries];
    snprintf(e->variant_id, sizeof(e->variant_id), "%s", variant_id);
    if (parent_id)
        snprintf(e->parent_id, sizeof(e->parent_id), "%s", parent_id);
    if (diff_path)
        snprintf(e->diff_path, sizeof(e->diff_path), "%s", diff_path);
    if (fitness)
        e->fitness = *fitness;
    e->generation = generation;
    e->children = 0;
    e->active = 1;

    /* Update parent's child count */
    if (parent_id) {
        for (int i = 0; i < st->n_entries; i++) {
            if (strcmp(st->entries[i].variant_id, parent_id) == 0) {
                st->entries[i].children++;
                break;
            }
        }
    }

    /* Track best */
    if (fitness && fitness->utility > st->best_utility) {
        st->best_utility = fitness->utility;
        st->best_idx = st->n_entries;
    }

    st->n_entries++;
    return st->n_entries - 1;
}

/**
 * @brief Select a parent variant for mutation.
 */
int archive_select_parent(archive_state_t *st, archive_select_t method) {
    if (!st || !st->initialized || st->n_entries == 0) return -1;

    switch (method) {
    case ARCHIVE_SELECT_BEST:
        return st->best_idx;

    case ARCHIVE_SELECT_RANDOM: {
        int idx = (int)(arch_rng(&st->rng_seed) % (uint32_t)st->n_entries);
        while (!st->entries[idx].active)
            idx = (idx + 1) % st->n_entries;
        return idx;
    }

    case ARCHIVE_SELECT_SCORE_PROP: {
        /* Score-proportional selection */
        double total = 0;
        for (int i = 0; i < st->n_entries; i++)
            if (st->entries[i].active)
                total += st->entries[i].fitness.utility;
        if (total <= 0) return 0;

        double r = (double)(arch_rng(&st->rng_seed) % 10000) / 10000.0 * total;
        double cumul = 0;
        for (int i = 0; i < st->n_entries; i++) {
            if (!st->entries[i].active) continue;
            cumul += st->entries[i].fitness.utility;
            if (cumul >= r) return i;
        }
        return st->n_entries - 1;
    }

    case ARCHIVE_SELECT_SCORE_CHILD: {
        /* score × 1/(1+children) — favors less-explored variants */
        double total = 0;
        for (int i = 0; i < st->n_entries; i++) {
            if (!st->entries[i].active) continue;
            total += st->entries[i].fitness.utility /
                     (1.0 + st->entries[i].children);
        }
        if (total <= 0) return 0;

        double r = (double)(arch_rng(&st->rng_seed) % 10000) / 10000.0 * total;
        double cumul = 0;
        for (int i = 0; i < st->n_entries; i++) {
            if (!st->entries[i].active) continue;
            cumul += st->entries[i].fitness.utility /
                     (1.0 + st->entries[i].children);
            if (cumul >= r) return i;
        }
        return st->n_entries - 1;
    }

    default:
        return 0;
    }
}

/**
 * @brief Get the lineage (ancestor chain) of a variant.
 *
 * @param lineage_out  Array to fill with variant IDs (oldest first)
 * @param max_depth    Maximum depth to traverse
 * @return             Number of ancestors found
 */
int archive_get_lineage(const archive_state_t *st, int variant_idx,
                         int *lineage_out, int max_depth) {
    if (!st || !st->initialized || !lineage_out) return -1;
    if (variant_idx < 0 || variant_idx >= st->n_entries) return -1;

    int depth = 0;
    int current = variant_idx;

    /* Traverse parent chain */
    int chain[ARCHIVE_MAX_VARIANTS];
    while (current >= 0 && depth < max_depth) {
        chain[depth++] = current;
        /* Find parent */
        const char *parent_id = st->entries[current].parent_id;
        int found = -1;
        for (int i = 0; i < st->n_entries; i++) {
            if (strcmp(st->entries[i].variant_id, parent_id) == 0) {
                found = i;
                break;
            }
        }
        current = found;
    }

    /* Reverse to oldest-first order */
    for (int i = 0; i < depth; i++)
        lineage_out[i] = chain[depth - 1 - i];

    return depth;
}

/**
 * @brief Get fitness of a variant.
 */
archive_fitness_t archive_get_fitness(const archive_state_t *st,
                                       int variant_idx) {
    archive_fitness_t zero = {0};
    if (!st || !st->initialized) return zero;
    if (variant_idx < 0 || variant_idx >= st->n_entries) return zero;
    return st->entries[variant_idx].fitness;
}

/**
 * @brief Get number of entries in archive.
 */
int archive_count(const archive_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->n_entries;
}

/**
 * @brief Get best utility score achieved.
 */
double archive_best_utility(const archive_state_t *st) {
    if (!st || !st->initialized) return 0.0;
    return st->best_utility;
}
