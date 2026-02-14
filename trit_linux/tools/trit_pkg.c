/**
 * @file trit_pkg.c
 * @brief Trit Linux — Ternary Package Manager Implementation
 *
 * Implements the T-Pkg system with trit-compressed archives, Guardian Trit
 * checksum validation, and Kleene-logic dependency resolution.
 *
 * Enhancement 4: "Package Management and Repository System"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "trit_pkg.h"

/* ==================================================================== */
/*  Helper: find package by name                                        */
/* ==================================================================== */

/**
 * @brief Find a package index by name.
 * @return Package index (>=0) or -1 if not found.
 */
static int find_package(const tpkg_repo_t *repo, const char *name) {
    if (!repo || !name) return -1;
    for (int i = 0; i < repo->package_count; i++) {
        if (strcmp(repo->packages[i].name, name) == 0) {
            return i;
        }
    }
    return -1;
}

/* ==================================================================== */
/*  Checksum — 9-trit Guardian Trit integrity check                     */
/* ==================================================================== */

void tpkg_checksum_compute(trit *checksum, const trit *data, int len) {
    if (!checksum || !data) return;

    /*
     * Guardian Trit checksum: accumulate trit values across 9 positions
     * with positional weighting (multiply by position mod 3) for better
     * error detection than simple XOR.
     */
    int accum[TPKG_CHECKSUM_TRITS] = {0};

    for (int i = 0; i < len; i++) {
        /* Weight by position: multiply by (i % 3 + 1) for diversity */
        int weight = (i % 3) + 1;
        accum[i % TPKG_CHECKSUM_TRITS] += data[i] * weight;
    }

    /* Reduce to balanced ternary */
    for (int i = 0; i < TPKG_CHECKSUM_TRITS; i++) {
        int v = ((accum[i] % 3) + 3) % 3;
        if (v == 0)      checksum[i] = 0;
        else if (v == 1) checksum[i] = 1;
        else             checksum[i] = -1;
    }
}

/* ==================================================================== */
/*  Repository Initialization                                           */
/* ==================================================================== */

int tpkg_init(tpkg_repo_t *repo) {
    if (!repo) return TPKG_ERR_IO;

    memset(repo, 0, sizeof(*repo));
    repo->initialized = 1;

    return TPKG_OK;
}

/* ==================================================================== */
/*  Package Addition                                                    */
/* ==================================================================== */

int tpkg_add(tpkg_repo_t *repo, const char *name, const char *desc,
             int version, const trit *data, int data_len) {
    if (!repo || !name || !repo->initialized) return TPKG_ERR_IO;
    if (repo->package_count >= TPKG_MAX_PACKAGES) return TPKG_ERR_FULL;

    /* Check for duplicate names */
    if (find_package(repo, name) >= 0) return TPKG_ERR_INSTALLED;

    /* Clamp data length to max */
    if (data_len > TPKG_MAX_DATA) data_len = TPKG_MAX_DATA;

    tpkg_package_t *pkg = &repo->packages[repo->package_count];
    memset(pkg, 0, sizeof(*pkg));

    /* Set package metadata */
    strncpy(pkg->name, name, TPKG_NAME_LEN - 1);
    if (desc) strncpy(pkg->description, desc, TPKG_DESC_LEN - 1);
    pkg->version = version;
    pkg->installed = 0;

    /* Copy package data */
    if (data && data_len > 0) {
        memcpy(pkg->data, data, sizeof(trit) * data_len);
        pkg->data_len = data_len;
        pkg->size_trits = data_len;
    }

    /* Compute integrity checksum */
    tpkg_checksum_compute(pkg->checksum, pkg->data, pkg->data_len);
    pkg->integrity = TRIT_TRUE; /* Freshly computed = verified */

    repo->package_count++;
    return TPKG_OK;
}

int tpkg_add_dep(tpkg_repo_t *repo, const char *pkg_name,
                 const char *dep_name, trit relation, int min_version) {
    if (!repo || !pkg_name || !dep_name) return TPKG_ERR_IO;

    int idx = find_package(repo, pkg_name);
    if (idx < 0) return TPKG_ERR_NOTFOUND;

    tpkg_package_t *pkg = &repo->packages[idx];
    if (pkg->dep_count >= TPKG_MAX_DEPS) return TPKG_ERR_FULL;

    /* Add dependency entry */
    tpkg_dep_t *dep = &pkg->deps[pkg->dep_count];
    strncpy(dep->name, dep_name, TPKG_NAME_LEN - 1);
    dep->relation = relation;
    dep->min_version = min_version;
    pkg->dep_count++;

    return TPKG_OK;
}

/* ==================================================================== */
/*  Dependency Resolution — Kleene Logic                                */
/* ==================================================================== */

int tpkg_resolve_deps(const tpkg_repo_t *repo, const char *name) {
    if (!repo || !name) return TPKG_ERR_IO;

    int idx = find_package(repo, name);
    if (idx < 0) return TPKG_ERR_NOTFOUND;

    const tpkg_package_t *pkg = &repo->packages[idx];

    /*
     * Evaluate each dependency using Kleene logic:
     *   Required (+1): dependency MUST be installed + version check
     *   Optional (0):  missing dependency is OK (proceed)
     *   Conflict (-1): dependency must NOT be installed
     */
    for (int i = 0; i < pkg->dep_count; i++) {
        const tpkg_dep_t *dep = &pkg->deps[i];
        int dep_idx = find_package(repo, dep->name);

        switch (dep->relation) {
            case TRIT_TRUE: /* Required */
                if (dep_idx < 0 || !repo->packages[dep_idx].installed) {
                    return TPKG_ERR_DEPFAIL; /* Required dep missing */
                }
                if (repo->packages[dep_idx].version < dep->min_version) {
                    return TPKG_ERR_DEPFAIL; /* Version too old */
                }
                break;

            case TRIT_UNKNOWN: /* Optional */
                /* OK whether present or not — Kleene Unknown propagates */
                break;

            case TRIT_FALSE: /* Conflict */
                if (dep_idx >= 0 && repo->packages[dep_idx].installed) {
                    return TPKG_ERR_CONFLICT; /* Conflicting pkg installed */
                }
                break;

            default:
                break;
        }
    }

    return TPKG_OK; /* All dependencies satisfied */
}

/* ==================================================================== */
/*  Install / Remove                                                    */
/* ==================================================================== */

int tpkg_install(tpkg_repo_t *repo, const char *name) {
    if (!repo || !name || !repo->initialized) return TPKG_ERR_IO;

    int idx = find_package(repo, name);
    if (idx < 0) return TPKG_ERR_NOTFOUND;
    if (repo->packages[idx].installed) return TPKG_ERR_INSTALLED;

    /* Resolve dependencies first */
    int dep_result = tpkg_resolve_deps(repo, name);
    if (dep_result != TPKG_OK) {
        repo->dep_conflicts++;
        return dep_result;
    }

    /* Verify integrity (checksum) */
    int verify_result = tpkg_verify(repo, name);
    if (verify_result != TPKG_OK) {
        return verify_result;
    }

    /* Mark as installed */
    repo->packages[idx].installed = 1;
    repo->installed_count++;
    repo->installs++;

    return TPKG_OK;
}

int tpkg_remove(tpkg_repo_t *repo, const char *name) {
    if (!repo || !name || !repo->initialized) return TPKG_ERR_IO;

    int idx = find_package(repo, name);
    if (idx < 0) return TPKG_ERR_NOTFOUND;
    if (!repo->packages[idx].installed) return TPKG_ERR_NOTFOUND;

    /* Uninstall */
    repo->packages[idx].installed = 0;
    repo->installed_count--;
    repo->removals++;

    return TPKG_OK;
}

/* ==================================================================== */
/*  Search and List                                                     */
/* ==================================================================== */

int tpkg_search(const tpkg_repo_t *repo, const char *query,
                tpkg_search_result_t *result) {
    if (!repo || !query || !result) return TPKG_ERR_IO;

    memset(result, 0, sizeof(*result));

    /* Simple substring search across package names */
    for (int i = 0; i < repo->package_count && result->count < TPKG_MAX_PACKAGES; i++) {
        if (strstr(repo->packages[i].name, query) != NULL) {
            result->indices[result->count++] = i;
        }
    }

    return result->count;
}

int tpkg_list_installed(const tpkg_repo_t *repo, tpkg_search_result_t *result) {
    if (!repo || !result) return TPKG_ERR_IO;

    memset(result, 0, sizeof(*result));

    for (int i = 0; i < repo->package_count && result->count < TPKG_MAX_PACKAGES; i++) {
        if (repo->packages[i].installed) {
            result->indices[result->count++] = i;
        }
    }

    return result->count;
}

int tpkg_is_installed(const tpkg_repo_t *repo, const char *name) {
    if (!repo || !name) return 0;
    int idx = find_package(repo, name);
    if (idx < 0) return 0;
    return repo->packages[idx].installed;
}

/* ==================================================================== */
/*  Integrity Verification                                              */
/* ==================================================================== */

int tpkg_verify(tpkg_repo_t *repo, const char *name) {
    if (!repo || !name) return TPKG_ERR_IO;

    int idx = find_package(repo, name);
    if (idx < 0) return TPKG_ERR_NOTFOUND;

    tpkg_package_t *pkg = &repo->packages[idx];

    /* Recompute checksum and compare */
    trit expected[TPKG_CHECKSUM_TRITS];
    tpkg_checksum_compute(expected, pkg->data, pkg->data_len);

    for (int i = 0; i < TPKG_CHECKSUM_TRITS; i++) {
        if (expected[i] != pkg->checksum[i]) {
            pkg->integrity = TRIT_FALSE; /* Corrupted */
            repo->checksum_fails++;
            return TPKG_ERR_CHECKSUM;
        }
    }

    pkg->integrity = TRIT_TRUE; /* Verified */
    return TPKG_OK;
}

/* ==================================================================== */
/*  Statistics                                                          */
/* ==================================================================== */

void tpkg_stats(const tpkg_repo_t *repo,
                int *total, int *installed, int *conflicts, int *checksum_fails) {
    if (!repo) return;
    if (total)          *total          = repo->package_count;
    if (installed)      *installed      = repo->installed_count;
    if (conflicts)      *conflicts      = repo->dep_conflicts;
    if (checksum_fails) *checksum_fails = repo->checksum_fails;
}
