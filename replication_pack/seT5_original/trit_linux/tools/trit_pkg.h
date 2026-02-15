/**
 * @file trit_pkg.h
 * @brief Trit Linux — Ternary Package Manager Header
 *
 * Defines the T-Pkg package management system: a ternary-native
 * apt-like package manager using TFS for storage and Balanced Ternary
 * Huffman Coding for compact archives. Includes dependency resolution
 * using Kleene logic (0 = optional dependency).
 *
 * Enhancement 4 from LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *   "Package Management and Repository System"
 *
 * Key features:
 *   - Package archive format with trit-compressed metadata
 *   - Guardian Trit checksum validation for integrity
 *   - Kleene dependency resolution (T=required, U=optional, F=conflict)
 *   - Package install, remove, search, list, verify commands
 *   - Repository manifest with version tracking
 *   - Radix guard: quarantine non-ternary dependencies
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_PKG_H
#define TRIT_LINUX_TRIT_PKG_H

#include "set5/trit.h"
#include "set5/tfs.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TPKG_MAX_PACKAGES    32    /* Max packages in repository           */
#define TPKG_MAX_DEPS        8     /* Max dependencies per package         */
#define TPKG_NAME_LEN        24    /* Max package name length              */
#define TPKG_DESC_LEN        64    /* Max description length               */
#define TPKG_MAX_DATA        512   /* Max package data trits               */
#define TPKG_CHECKSUM_TRITS  9     /* Guardian Trit checksum (3^2=9 trits) */

/* Error codes */
#define TPKG_OK              0
#define TPKG_ERR_NOTFOUND   (-1)
#define TPKG_ERR_FULL       (-2)
#define TPKG_ERR_CONFLICT   (-3)
#define TPKG_ERR_CHECKSUM   (-4)
#define TPKG_ERR_DEPFAIL    (-5)
#define TPKG_ERR_INSTALLED  (-6)
#define TPKG_ERR_IO         (-7)

/* Dependency relation types (Kleene logic) */
#define TPKG_DEP_REQUIRED    TRIT_TRUE     /* +1: Must be installed        */
#define TPKG_DEP_OPTIONAL    TRIT_UNKNOWN  /*  0: Nice to have             */
#define TPKG_DEP_CONFLICT    TRIT_FALSE    /* -1: Must NOT be installed    */

/* ==== Types ============================================================= */

/**
 * @brief Package dependency descriptor.
 *
 * Uses Kleene logic for dependency semantics:
 *   +1 (True)    = required (install fails if missing)
 *    0 (Unknown) = optional (install proceeds if missing)
 *   -1 (False)   = conflict (install fails if present)
 */
typedef struct {
    char name[TPKG_NAME_LEN]; /**< Dependency package name               */
    trit relation;             /**< +1=required, 0=optional, -1=conflict  */
    int  min_version;          /**< Minimum version (×100, e.g. 100=v1.0) */
} tpkg_dep_t;

/**
 * @brief Package descriptor.
 *
 * Describes a single package in the repository with name, version,
 * dependencies, integrity checksum, and install state.
 */
typedef struct {
    char         name[TPKG_NAME_LEN];  /**< Package name                  */
    char         description[TPKG_DESC_LEN]; /**< Human-readable desc     */
    int          version;              /**< Version × 100 (e.g. 100=v1.0) */
    int          installed;            /**< 1 = installed, 0 = available   */
    int          size_trits;           /**< Package size in trits          */

    /* Dependencies */
    tpkg_dep_t   deps[TPKG_MAX_DEPS]; /**< Dependency list                */
    int          dep_count;            /**< Number of dependencies         */

    /* Package data (trit-compressed payload) */
    trit         data[TPKG_MAX_DATA];  /**< Package content (trits)        */
    int          data_len;             /**< Actual data length              */

    /* Integrity */
    trit         checksum[TPKG_CHECKSUM_TRITS]; /**< Guardian Trit checksum */
    trit         integrity;            /**< T=verified, U=unchecked, F=bad */
} tpkg_package_t;

/**
 * @brief Package search result.
 */
typedef struct {
    int  indices[TPKG_MAX_PACKAGES];   /**< Indices into repo packages[]   */
    int  count;                        /**< Number of results              */
} tpkg_search_result_t;

/**
 * @brief Package repository state.
 *
 * Central repository containing all available and installed packages.
 * Includes dependency resolver and integrity checking.
 */
typedef struct {
    tpkg_package_t packages[TPKG_MAX_PACKAGES]; /**< Package table        */
    int            package_count;       /**< Total packages in repo        */
    int            installed_count;     /**< Currently installed packages  */
    int            initialized;         /**< 1 = repo ready                */

    /* Statistics */
    int            installs;            /**< Successful installs           */
    int            removals;            /**< Successful removals           */
    int            checksum_fails;      /**< Integrity check failures      */
    int            dep_conflicts;       /**< Dependency conflicts detected */
} tpkg_repo_t;

/* ==== Repository API ==================================================== */

/** Initialize the package repository */
int tpkg_init(tpkg_repo_t *repo);

/** Add a package to the repository (not yet installed) */
int tpkg_add(tpkg_repo_t *repo, const char *name, const char *desc,
             int version, const trit *data, int data_len);

/** Add a dependency to an existing package */
int tpkg_add_dep(tpkg_repo_t *repo, const char *pkg_name,
                 const char *dep_name, trit relation, int min_version);

/* ==== Install / Remove ================================================== */

/** Install a package (checks dependencies and integrity) */
int tpkg_install(tpkg_repo_t *repo, const char *name);

/** Remove an installed package */
int tpkg_remove(tpkg_repo_t *repo, const char *name);

/* ==== Query ============================================================= */

/** Search for packages by name substring */
int tpkg_search(const tpkg_repo_t *repo, const char *query,
                tpkg_search_result_t *result);

/** List all installed packages (returns count) */
int tpkg_list_installed(const tpkg_repo_t *repo, tpkg_search_result_t *result);

/** Check if a package is installed */
int tpkg_is_installed(const tpkg_repo_t *repo, const char *name);

/* ==== Integrity ========================================================= */

/** Compute Guardian Trit checksum for a package */
void tpkg_checksum_compute(trit *checksum, const trit *data, int len);

/** Verify package integrity */
int tpkg_verify(tpkg_repo_t *repo, const char *name);

/* ==== Dependency Resolution ============================================= */

/** Resolve dependencies using Kleene logic (returns 0 if all satisfied) */
int tpkg_resolve_deps(const tpkg_repo_t *repo, const char *name);

/* ==== Statistics ========================================================= */

/** Get repository statistics */
void tpkg_stats(const tpkg_repo_t *repo,
                int *total, int *installed, int *conflicts, int *checksum_fails);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_PKG_H */
