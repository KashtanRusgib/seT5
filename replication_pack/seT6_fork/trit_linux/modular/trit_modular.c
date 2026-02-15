/**
 * @file trit_modular.c
 * @brief seT6 Trit Linux — LEGO-Like Modularity Framework Implementation
 *
 * Implements Arch Linux–inspired modular design:
 *   - Module registration, loading, unloading with dependency checks
 *   - Drop-in config overrides (key=value, like systemd .d/ dirs)
 *   - Radix Integrity Guard to reject binary creep
 *   - Strip binary emulation for ternary purity upgrades
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "trit_modular.h"

/* ==================================================================== */
/*  Internal helpers                                                    */
/* ==================================================================== */

static tmod_module_t *find_module(tmod_framework_t *fw, const char *name) {
    if (!fw || !name) return NULL;
    for (int i = 0; i < fw->module_count; i++) {
        if (strncmp(fw->modules[i].name, name, TMOD_NAME_LEN) == 0) {
            return &fw->modules[i];
        }
    }
    return NULL;
}

/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

int tmod_init(tmod_framework_t *fw) {
    if (!fw) return TMOD_ERR_INIT;

    memset(fw, 0, sizeof(*fw));
    fw->radix_guard.guard_status = TRIT_TRUE;  /* Clean until proven otherwise */
    fw->initialized = 1;
    return TMOD_OK;
}

/* ==================================================================== */
/*  Module Registration                                                 */
/* ==================================================================== */

int tmod_register(tmod_framework_t *fw, const char *name, int radix_purity) {
    if (!fw || !fw->initialized || !name) return TMOD_ERR_INIT;
    if (fw->module_count >= TMOD_MAX_MODULES) return TMOD_ERR_FULL;

    /* Reject if already registered */
    if (find_module(fw, name)) return TMOD_ERR_FULL;

    tmod_module_t *mod = &fw->modules[fw->module_count];
    memset(mod, 0, sizeof(*mod));

    strncpy(mod->name, name, TMOD_NAME_LEN - 1);
    mod->id = fw->module_count;
    mod->state = TMOD_STATE_UNLOADED;
    mod->radix_purity = radix_purity;
    mod->dep_count = 0;
    mod->config_count = 0;

    fw->module_count++;
    return mod->id;
}

/* ==================================================================== */
/*  Dependency Management                                               */
/* ==================================================================== */

int tmod_add_dependency(tmod_framework_t *fw, const char *module, const char *dep) {
    if (!fw || !fw->initialized) return TMOD_ERR_INIT;

    tmod_module_t *mod = find_module(fw, module);
    if (!mod) return TMOD_ERR_NOTFOUND;
    if (mod->dep_count >= TMOD_MAX_DEPS) return TMOD_ERR_FULL;

    strncpy(mod->deps[mod->dep_count], dep, TMOD_NAME_LEN - 1);
    mod->dep_count++;
    return TMOD_OK;
}

int tmod_deps_satisfied(tmod_framework_t *fw, const char *name) {
    if (!fw || !fw->initialized) return 0;

    tmod_module_t *mod = find_module(fw, name);
    if (!mod) return 0;

    for (int i = 0; i < mod->dep_count; i++) {
        tmod_module_t *dep = find_module(fw, mod->deps[i]);
        if (!dep || dep->state < TMOD_STATE_LOADED) {
            return 0;  /* Dependency not loaded */
        }
    }
    return 1;  /* All deps satisfied */
}

/* ==================================================================== */
/*  Drop-in Configuration                                               */
/* ==================================================================== */

int tmod_add_config(tmod_framework_t *fw, const char *module,
                    const char *key, const char *value) {
    if (!fw || !fw->initialized) return TMOD_ERR_INIT;
    if (!key || !value) return TMOD_ERR_CONFIG;

    tmod_module_t *mod = find_module(fw, module);
    if (!mod) return TMOD_ERR_NOTFOUND;
    if (mod->config_count >= TMOD_MAX_CONFIGS) return TMOD_ERR_FULL;

    /* Check for existing key — override if found */
    for (int i = 0; i < mod->config_count; i++) {
        if (strncmp(mod->configs[i].key, key, TMOD_CFG_KEY_LEN) == 0) {
            strncpy(mod->configs[i].value, value, TMOD_CFG_VAL_LEN - 1);
            mod->configs[i].active = 1;
            return TMOD_OK;
        }
    }

    tmod_config_entry_t *cfg = &mod->configs[mod->config_count];
    strncpy(cfg->key, key, TMOD_CFG_KEY_LEN - 1);
    strncpy(cfg->value, value, TMOD_CFG_VAL_LEN - 1);
    cfg->active = 1;
    mod->config_count++;
    return TMOD_OK;
}

const char *tmod_get_config(tmod_framework_t *fw, const char *module,
                            const char *key) {
    if (!fw || !fw->initialized || !key) return NULL;

    tmod_module_t *mod = find_module(fw, module);
    if (!mod) return NULL;

    for (int i = 0; i < mod->config_count; i++) {
        if (mod->configs[i].active &&
            strncmp(mod->configs[i].key, key, TMOD_CFG_KEY_LEN) == 0) {
            return mod->configs[i].value;
        }
    }
    return NULL;
}

/* ==================================================================== */
/*  Module Load / Unload                                                */
/* ==================================================================== */

int tmod_load(tmod_framework_t *fw, const char *name) {
    if (!fw || !fw->initialized) return TMOD_ERR_INIT;

    tmod_module_t *mod = find_module(fw, name);
    if (!mod) return TMOD_ERR_NOTFOUND;

    /* Check dependencies */
    if (!tmod_deps_satisfied(fw, name)) {
        mod->state = TMOD_STATE_FAILED;
        return TMOD_ERR_DEPENDENCY;
    }

    /* Radix purity check — reject binary-only modules in ternary mode */
    if (mod->radix_purity < TMOD_RADIX_MIXED) {
        /* Binary emulation module — warn via radix guard */
        fw->radix_guard.violations_found++;
        fw->radix_guard.guard_status = TRIT_UNKNOWN;  /* Warning state */
    }

    mod->state = TMOD_STATE_ACTIVE;
    mod->load_count++;
    return TMOD_OK;
}

int tmod_unload(tmod_framework_t *fw, const char *name) {
    if (!fw || !fw->initialized) return TMOD_ERR_INIT;

    tmod_module_t *mod = find_module(fw, name);
    if (!mod) return TMOD_ERR_NOTFOUND;

    mod->state = TMOD_STATE_UNLOADED;
    return TMOD_OK;
}

/* ==================================================================== */
/*  Radix Integrity Guard                                               */
/* ==================================================================== */

int tmod_radix_scan(tmod_framework_t *fw) {
    if (!fw || !fw->initialized) return TMOD_ERR_INIT;

    fw->radix_guard.scans_performed++;
    fw->radix_guard.violations_found = 0;
    fw->radix_guard.modules_cleared = 0;
    fw->radix_guard.guard_status = TRIT_TRUE;

    for (int i = 0; i < fw->module_count; i++) {
        tmod_module_t *mod = &fw->modules[i];

        if (mod->radix_purity == TMOD_RADIX_BINARY_EMU ||
            mod->radix_purity == TMOD_RADIX_MIXED) {
            fw->radix_guard.violations_found++;
            fw->radix_guard.guard_status = TRIT_FALSE;  /* Impure */
        } else {
            fw->radix_guard.modules_cleared++;
        }
    }

    if (fw->radix_guard.violations_found == 0) {
        fw->radix_guard.guard_status = TRIT_TRUE;  /* All clean */
    }

    return fw->radix_guard.violations_found;
}

/* ==================================================================== */
/*  Module Lookup                                                       */
/* ==================================================================== */

tmod_module_t *tmod_find(tmod_framework_t *fw, const char *name) {
    return find_module(fw, name);
}

int tmod_count(const tmod_framework_t *fw) {
    if (!fw) return 0;
    return fw->module_count;
}

/* ==================================================================== */
/*  Strip Binary Emulation                                              */
/* ==================================================================== */

int tmod_strip_binary_emu(tmod_framework_t *fw, const char *name) {
    if (!fw || !fw->initialized) return TMOD_ERR_INIT;

    tmod_module_t *mod = find_module(fw, name);
    if (!mod) return TMOD_ERR_NOTFOUND;

    if (mod->radix_purity == TMOD_RADIX_BINARY_EMU) {
        mod->radix_purity = TMOD_RADIX_TERNARY;
        return TMOD_OK;
    }

    /* Already pure or mixed — no-op */
    return TMOD_OK;
}
