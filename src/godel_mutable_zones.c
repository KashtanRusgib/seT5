/**
 * @file godel_mutable_zones.c
 * @brief T-057: Gödel Machine Mutation Scope Controller
 *
 * Defines which source files/functions are MUTABLE vs IMMUTABLE.
 * Maps to DGM's constrained editing pattern.
 *
 * Zone types:
 *   MUTABLE    — scheduler heuristics, allocator policies, compression params
 *   IMMUTABLE  — crown jewels (Kleene K₃, SIMD, tcrypto, GF(3) Hamming)
 *   RESTRICTED — modifiable only with additional proof obligations
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* ── Configuration ── */
#define ZONE_MAX_RULES     256
#define ZONE_MAX_PATH_LEN  256
#define ZONE_MAX_FUNC_LEN  128

/* ── Zone types ── */
typedef enum {
    ZONE_MUTABLE    = 0,   /* free to modify */
    ZONE_IMMUTABLE  = 1,   /* NEVER modify — crown jewels */
    ZONE_RESTRICTED = 2,   /* modify only with extra proof */
} zone_type_t;

/* ── Zone rule ── */
typedef struct {
    char        filepath[ZONE_MAX_PATH_LEN];  /* glob pattern or exact path */
    char        function[ZONE_MAX_FUNC_LEN];  /* "*" for entire file */
    zone_type_t type;
    const char *reason;
} zone_rule_t;

/* ── Built-in crown jewel rules ── */
static const zone_rule_t crown_jewel_rules[] = {
    /* Crown Jewel #1: Kleene K₃ logic */
    { "include/set5/trit.h",     "trit_and",           ZONE_IMMUTABLE, "Kleene AND — TritKleene.thy verified" },
    { "include/set5/trit.h",     "trit_or",            ZONE_IMMUTABLE, "Kleene OR — TritKleene.thy verified" },
    { "include/set5/trit.h",     "trit_not",           ZONE_IMMUTABLE, "Kleene NOT — TritKleene.thy verified" },
    { "include/set5/trit.h",     "trit_implies",       ZONE_IMMUTABLE, "Kleene IMPLIES — derived" },
    { "include/set5/trit.h",     "trit_equiv",         ZONE_IMMUTABLE, "Kleene EQUIV — derived" },

    /* Crown Jewel #2: SIMD packed64 */
    { "include/set5/trit.h",     "trit_and_packed64",  ZONE_IMMUTABLE, "SIMD AND — SIMDPacked.thy verified" },
    { "include/set5/trit.h",     "trit_or_packed64",   ZONE_IMMUTABLE, "SIMD OR — SIMDPacked.thy verified" },
    { "include/set5/trit.h",     "trit_not_packed64",  ZONE_IMMUTABLE, "SIMD NOT — SIMDPacked.thy verified" },

    /* Crown Jewel #3: pack/unpack */
    { "include/set5/trit.h",     "trit_pack",          ZONE_IMMUTABLE, "2-bit encoding" },
    { "include/set5/trit.h",     "trit_unpack",        ZONE_IMMUTABLE, "2-bit decoding" },

    /* Crown Jewel #4: Crypto S-box */
    { "src/trit_crypto.c",       "sbox",               ZONE_IMMUTABLE, "Ternary S-box — cyclic rotation" },
    { "src/trit_crypto.c",       "sbox_inv",           ZONE_IMMUTABLE, "Inverse S-box" },
    { "include/set5/trit_crypto.h", "tcrypto_trit_xor", ZONE_IMMUTABLE, "Balanced mod-3 XOR" },

    /* Crown Jewel #5: GF(3) Hamming */
    { "src/fault_tolerant_network.c", "ternary_hamming_encode", ZONE_IMMUTABLE, "GF(3) Hamming — TernaryArith.thy" },
    { "src/fault_tolerant_network.c", "ternary_hamming_decode", ZONE_IMMUTABLE, "GF(3) Hamming decode" },

    /* Crown Jewel #6: trit_cast bridge */
    { "include/set5/trit_cast.h", "*",                  ZONE_IMMUTABLE, "Type bridge — verified" },

    /* Crown Jewel #7: Isabelle proofs */
    { "proof/*.thy",              "*",                  ZONE_IMMUTABLE, "Formal verification proofs" },

    /* Restricted zones: modifiable with proof */
    { "src/scheduler.c",         "*",                  ZONE_RESTRICTED, "Scheduler — heuristics mutable, invariants protected" },
    { "src/memory.c",            "*",                  ZONE_RESTRICTED, "Memory allocator — policies mutable" },

    /* Mutable zones */
    { "src/ternary_database.c",  "ternary_huffman_build", ZONE_MUTABLE, "Compression tuning" },
    { "src/ternary_weight_quantizer.c", "*",           ZONE_MUTABLE, "Quantizer parameters" },
    { "tests/*.c",               "*",                  ZONE_MUTABLE, "Test files — always mutable" },
};

#define N_CROWN_RULES (sizeof(crown_jewel_rules) / sizeof(crown_jewel_rules[0]))

/* ── State ── */
typedef struct {
    zone_rule_t custom_rules[ZONE_MAX_RULES];
    int         n_custom_rules;
    int         violations;
    int         initialized;
} zone_state_t;

/* ── Simple glob match (supports * at start/end) ── */
static int glob_match(const char *pattern, const char *str) {
    if (strcmp(pattern, "*") == 0) return 1;

    /* Check if pattern has wildcard at start */
    int plen = (int)strlen(pattern);
    int slen = (int)strlen(str);

    if (plen > 0 && pattern[0] == '*') {
        /* Match suffix */
        const char *suffix = pattern + 1;
        int sufflen = plen - 1;
        if (slen >= sufflen && strcmp(str + slen - sufflen, suffix) == 0)
            return 1;
    }

    if (plen > 0 && pattern[plen-1] == '*') {
        /* Match prefix */
        if (strncmp(str, pattern, plen - 1) == 0)
            return 1;
    }

    /* Exact match */
    return strcmp(pattern, str) == 0;
}

/* ── API ── */

int zone_init(zone_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

/**
 * @brief Check the mutation zone for a file/function.
 *
 * @return ZONE_MUTABLE, ZONE_IMMUTABLE, or ZONE_RESTRICTED
 */
zone_type_t zone_check(const zone_state_t *st, const char *filepath,
                        const char *function_name) {
    if (!filepath) return ZONE_IMMUTABLE; /* default safe */

    /* Check built-in crown jewel rules first */
    for (int i = 0; i < (int)N_CROWN_RULES; i++) {
        const zone_rule_t *r = &crown_jewel_rules[i];
        if (glob_match(r->filepath, filepath)) {
            if (function_name && glob_match(r->function, function_name))
                return r->type;
            if (strcmp(r->function, "*") == 0)
                return r->type;
        }
    }

    /* Check custom rules */
    if (st && st->initialized) {
        for (int i = 0; i < st->n_custom_rules; i++) {
            const zone_rule_t *r = &st->custom_rules[i];
            if (glob_match(r->filepath, filepath)) {
                if (function_name && glob_match(r->function, function_name))
                    return r->type;
                if (strcmp(r->function, "*") == 0)
                    return r->type;
            }
        }
    }

    /* Default: mutable if not in any rule */
    return ZONE_MUTABLE;
}

/**
 * @brief Add a custom zone rule.
 */
int zone_add_rule(zone_state_t *st, const char *filepath,
                   const char *function_name, zone_type_t type) {
    if (!st || !st->initialized || !filepath) return -1;
    if (st->n_custom_rules >= ZONE_MAX_RULES) return -1;

    zone_rule_t *r = &st->custom_rules[st->n_custom_rules];
    snprintf(r->filepath, sizeof(r->filepath), "%s", filepath);
    if (function_name)
        snprintf(r->function, sizeof(r->function), "%s", function_name);
    else
        snprintf(r->function, sizeof(r->function), "*");
    r->type = type;
    r->reason = "custom rule";

    st->n_custom_rules++;
    return 0;
}

/**
 * @brief Validate a patch: check all modified files/functions against zones.
 *
 * @param filepaths  Array of modified file paths
 * @param functions  Array of modified function names (parallel to filepaths)
 * @param count      Number of modifications
 * @return 0 if all modifications are in MUTABLE zones, -1 if any IMMUTABLE hit
 */
int zone_validate_patch(zone_state_t *st, const char **filepaths,
                         const char **functions, int count) {
    if (!st || !filepaths || count <= 0) return -1;

    for (int i = 0; i < count; i++) {
        zone_type_t z = zone_check(st, filepaths[i],
                                     functions ? functions[i] : NULL);
        if (z == ZONE_IMMUTABLE) {
            st->violations++;
            return -1; /* HARD REJECT */
        }
    }
    return 0;
}

/**
 * @brief Get violation count.
 */
int zone_get_violations(const zone_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->violations;
}

/**
 * @brief Check if a specific crown jewel function is protected.
 */
int zone_is_crown_jewel(const char *filepath, const char *function_name) {
    for (int i = 0; i < (int)N_CROWN_RULES; i++) {
        const zone_rule_t *r = &crown_jewel_rules[i];
        if (r->type != ZONE_IMMUTABLE) continue;
        if (glob_match(r->filepath, filepath) &&
            (strcmp(r->function, "*") == 0 ||
             (function_name && glob_match(r->function, function_name))))
            return 1;
    }
    return 0;
}
