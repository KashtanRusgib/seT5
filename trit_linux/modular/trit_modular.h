/**
 * @file trit_modular.h
 * @brief seT6 Trit Linux — LEGO-Like Modularity Framework Header
 *
 * Implements Arch Linux–inspired modular design for seT6 user-space:
 *   - Standalone, testable module units with dependency tracking
 *   - Drop-in configuration overrides (like systemd .d/ dirs)
 *   - Radix Integrity Guard to reject binary creep
 *   - Module rebuild/strip capabilities for ternary purity
 *
 * Each module registers with the framework and declares its dependencies,
 * configuration overrides, and radix purity level. The framework enforces
 * that no module introduces binary-only operations into the ternary stack.
 *
 * Adapted from Arch Linux's minimal, LEGO-like package philosophy.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_MODULAR_H
#define TRIT_LINUX_MODULAR_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TMOD_MAX_MODULES       32     /* Max registered modules             */
#define TMOD_MAX_DEPS          8      /* Max dependencies per module        */
#define TMOD_MAX_CONFIGS       16     /* Max drop-in config overrides       */
#define TMOD_NAME_LEN          32     /* Max module name length             */
#define TMOD_CFG_KEY_LEN       32     /* Max config key length              */
#define TMOD_CFG_VAL_LEN       64     /* Max config value length            */

/* Module states */
#define TMOD_STATE_UNLOADED    0
#define TMOD_STATE_LOADED      1
#define TMOD_STATE_ACTIVE      2
#define TMOD_STATE_FAILED      (-1)

/* Radix purity levels */
#define TMOD_RADIX_TERNARY     3      /* Pure ternary — no binary ops       */
#define TMOD_RADIX_MIXED       2      /* Mixed radix (multi-radix bridge)   */
#define TMOD_RADIX_BINARY_EMU  1      /* Binary emulation (to be stripped)  */

/* Error codes */
#define TMOD_OK                0
#define TMOD_ERR_INIT          (-1)
#define TMOD_ERR_FULL          (-2)
#define TMOD_ERR_NOTFOUND      (-3)
#define TMOD_ERR_DEPENDENCY    (-4)
#define TMOD_ERR_RADIX_IMPURE  (-5)
#define TMOD_ERR_CONFIG        (-6)

/* ==== Types ============================================================= */

/**
 * @brief Drop-in configuration entry (key=value pair).
 *
 * Like Arch/systemd override.conf drop-ins — allows overriding default
 * module parameters without modifying the module itself.
 */
typedef struct {
    char key[TMOD_CFG_KEY_LEN];       /**< Config key name                  */
    char value[TMOD_CFG_VAL_LEN];     /**< Config value string              */
    int  active;                       /**< 1 = override is in effect        */
} tmod_config_entry_t;

/**
 * @brief Module descriptor — a standalone, testable unit.
 */
typedef struct {
    char  name[TMOD_NAME_LEN];         /**< Module name (e.g., "tipc")      */
    int   id;                          /**< Unique module ID                */
    int   state;                       /**< TMOD_STATE_*                    */
    int   radix_purity;                /**< TMOD_RADIX_* level              */

    /* Dependencies (by name) */
    char  deps[TMOD_MAX_DEPS][TMOD_NAME_LEN]; /**< Dependency module names */
    int   dep_count;                   /**< Number of dependencies          */

    /* Drop-in config overrides */
    tmod_config_entry_t configs[TMOD_MAX_CONFIGS];
    int   config_count;                /**< Number of config overrides      */

    /* Stats */
    int   load_count;                  /**< Times this module was loaded    */
    int   test_pass_count;             /**< Self-test pass count            */
    int   test_fail_count;             /**< Self-test fail count            */
} tmod_module_t;

/**
 * @brief Radix Integrity Guard state.
 *
 * Scans modules for binary creep — flags any module that introduces
 * binary-only operations into the ternary pipeline.
 */
typedef struct {
    int  scans_performed;              /**< Total radix scans               */
    int  violations_found;             /**< Binary creep violations         */
    int  modules_cleared;              /**< Modules passing radix check     */
    trit guard_status;                 /**< +1=clean, 0=warning, -1=impure  */
} tmod_radix_guard_t;

/**
 * @brief Module framework state.
 */
typedef struct {
    tmod_module_t      modules[TMOD_MAX_MODULES];
    int                module_count;
    tmod_radix_guard_t radix_guard;
    int                initialized;
} tmod_framework_t;

/* ==== API =============================================================== */

/** Initialize the modularity framework. */
int tmod_init(tmod_framework_t *fw);

/** Register a new module with given name and radix purity. */
int tmod_register(tmod_framework_t *fw, const char *name, int radix_purity);

/** Add a dependency to a module (by module name). */
int tmod_add_dependency(tmod_framework_t *fw, const char *module, const char *dep);

/** Add a drop-in config override to a module. */
int tmod_add_config(tmod_framework_t *fw, const char *module,
                    const char *key, const char *value);

/** Get a config value for a module (returns NULL if not found). */
const char *tmod_get_config(tmod_framework_t *fw, const char *module,
                            const char *key);

/** Load a module (checks dependencies first). */
int tmod_load(tmod_framework_t *fw, const char *name);

/** Unload a module. */
int tmod_unload(tmod_framework_t *fw, const char *name);

/** Run Radix Integrity Guard scan — checks all modules for binary creep. */
int tmod_radix_scan(tmod_framework_t *fw);

/** Find a module by name (returns pointer or NULL). */
tmod_module_t *tmod_find(tmod_framework_t *fw, const char *name);

/** Check if all dependencies of a module are satisfied. */
int tmod_deps_satisfied(tmod_framework_t *fw, const char *name);

/** Get module count. */
int tmod_count(const tmod_framework_t *fw);

/** Strip binary emulation from a module (upgrade to ternary purity). */
int tmod_strip_binary_emu(tmod_framework_t *fw, const char *name);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_MODULAR_H */
