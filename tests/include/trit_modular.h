/**
 * @file trit_modular.h
 * @brief seT6 — LEGO-Like Modular Framework (inline implementation)
 * SPDX-License-Identifier: GPL-2.0
 */
#ifndef TRIT_MODULAR_H
#define TRIT_MODULAR_H

#include <string.h>
#include <stdint.h>
#include "set5/trit.h"

/* Error codes */
#define TMOD_OK              0
#define TMOD_ERR_INIT       (-1)
#define TMOD_ERR_FULL       (-2)
#define TMOD_ERR_NOTFOUND   (-3)
#define TMOD_ERR_DEPENDENCY (-4)

/* Radix purity tags */
#define TMOD_RADIX_TERNARY    0
#define TMOD_RADIX_BINARY_EMU 1

/* Module states */
#define TMOD_STATE_UNLOADED 0
#define TMOD_STATE_ACTIVE   1
#define TMOD_STATE_FAILED   2

#define TMOD_MAX_MODULES 16
#define TMOD_MAX_DEPS    8
#define TMOD_MAX_CONFIGS 16
#define TMOD_NAME_LEN    32
#define TMOD_CFG_LEN     64

typedef struct {
    char name[TMOD_NAME_LEN];
    int  radix_purity;
    int  state;
    char deps[TMOD_MAX_DEPS][TMOD_NAME_LEN];
    int  dep_count;
} tmod_module_t;

typedef struct {
    char module[TMOD_NAME_LEN];
    char key[TMOD_CFG_LEN];
    char value[TMOD_CFG_LEN];
} tmod_config_t;

typedef struct {
    trit guard_status;
    int    modules_cleared;
    int    scans_performed;
} tmod_radix_guard_t;

typedef struct {
    tmod_module_t    modules[TMOD_MAX_MODULES];
    int              module_count;
    tmod_config_t    configs[TMOD_MAX_CONFIGS];
    int              config_count;
    tmod_radix_guard_t radix_guard;
    int              initialized;
} tmod_framework_t;

static inline int tmod_init(tmod_framework_t *fw) {
    if (!fw) return TMOD_ERR_INIT;
    memset(fw, 0, sizeof(*fw));
    fw->radix_guard.guard_status = TRIT_TRUE;
    fw->initialized = 1;
    return TMOD_OK;
}

static inline int tmod_count(const tmod_framework_t *fw) {
    return fw ? fw->module_count : 0;
}

static inline int tmod_register(tmod_framework_t *fw, const char *name, int radix) {
    if (!fw || !name) return TMOD_ERR_INIT;
    for (int i = 0; i < fw->module_count; i++)
        if (strcmp(fw->modules[i].name, name) == 0) return TMOD_ERR_FULL;
    if (fw->module_count >= TMOD_MAX_MODULES) return TMOD_ERR_FULL;
    int id = fw->module_count++;
    memset(&fw->modules[id], 0, sizeof(tmod_module_t));
    strncpy(fw->modules[id].name, name, TMOD_NAME_LEN - 1);
    fw->modules[id].radix_purity = radix;
    fw->modules[id].state = TMOD_STATE_UNLOADED;
    return id;
}

static inline tmod_module_t *tmod_find(tmod_framework_t *fw, const char *name) {
    if (!fw || !name) return NULL;
    for (int i = 0; i < fw->module_count; i++)
        if (strcmp(fw->modules[i].name, name) == 0) return &fw->modules[i];
    return NULL;
}

static inline int tmod_add_dependency(tmod_framework_t *fw, const char *mod, const char *dep) {
    tmod_module_t *m = tmod_find(fw, mod);
    if (!m) return TMOD_ERR_NOTFOUND;
    if (m->dep_count >= TMOD_MAX_DEPS) return TMOD_ERR_FULL;
    strncpy(m->deps[m->dep_count++], dep, TMOD_NAME_LEN - 1);
    return TMOD_OK;
}

static inline int tmod_deps_satisfied(tmod_framework_t *fw, const char *name) {
    tmod_module_t *m = tmod_find(fw, name);
    if (!m) return 0;
    for (int i = 0; i < m->dep_count; i++) {
        tmod_module_t *d = tmod_find(fw, m->deps[i]);
        if (!d || d->state != TMOD_STATE_ACTIVE) return 0;
    }
    return 1;
}

static inline int tmod_load(tmod_framework_t *fw, const char *name) {
    tmod_module_t *m = tmod_find(fw, name);
    if (!m) return TMOD_ERR_NOTFOUND;
    if (!tmod_deps_satisfied(fw, name)) { m->state = TMOD_STATE_FAILED; return TMOD_ERR_DEPENDENCY; }
    m->state = TMOD_STATE_ACTIVE;
    return TMOD_OK;
}

static inline int tmod_unload(tmod_framework_t *fw, const char *name) {
    tmod_module_t *m = tmod_find(fw, name);
    if (!m) return TMOD_ERR_NOTFOUND;
    m->state = TMOD_STATE_UNLOADED;
    return TMOD_OK;
}

static inline int tmod_add_config(tmod_framework_t *fw, const char *mod, const char *key, const char *val) {
    if (!tmod_find(fw, mod)) return TMOD_ERR_NOTFOUND;
    /* Override existing */
    for (int i = 0; i < fw->config_count; i++) {
        if (strcmp(fw->configs[i].module, mod) == 0 && strcmp(fw->configs[i].key, key) == 0) {
            strncpy(fw->configs[i].value, val, TMOD_CFG_LEN - 1);
            return TMOD_OK;
        }
    }
    if (fw->config_count >= TMOD_MAX_CONFIGS) return TMOD_ERR_FULL;
    int c = fw->config_count++;
    strncpy(fw->configs[c].module, mod, TMOD_NAME_LEN - 1);
    strncpy(fw->configs[c].key, key, TMOD_CFG_LEN - 1);
    strncpy(fw->configs[c].value, val, TMOD_CFG_LEN - 1);
    return TMOD_OK;
}

static inline const char *tmod_get_config(tmod_framework_t *fw, const char *mod, const char *key) {
    for (int i = 0; i < fw->config_count; i++)
        if (strcmp(fw->configs[i].module, mod) == 0 && strcmp(fw->configs[i].key, key) == 0)
            return fw->configs[i].value;
    return NULL;
}

static inline int tmod_radix_scan(tmod_framework_t *fw) {
    int violations = 0, cleared = 0;
    for (int i = 0; i < fw->module_count; i++) {
        if (fw->modules[i].radix_purity == TMOD_RADIX_BINARY_EMU) violations++;
        else cleared++;
    }
    fw->radix_guard.modules_cleared = cleared;
    fw->radix_guard.guard_status = violations ? TRIT_FALSE : TRIT_TRUE;
    fw->radix_guard.scans_performed++;
    return violations;
}

static inline int tmod_strip_binary_emu(tmod_framework_t *fw, const char *name) {
    tmod_module_t *m = tmod_find(fw, name);
    if (!m) return TMOD_ERR_NOTFOUND;
    m->radix_purity = TMOD_RADIX_TERNARY;
    return TMOD_OK;
}

#endif /* TRIT_MODULAR_H */
