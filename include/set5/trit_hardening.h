/**
 * @file trit_hardening.h
 * @brief seT6 Trit Linux — Attack Surface Reduction & Hardening Header
 *
 * Implements Arch Linux–inspired hardening for seT6 user-space:
 *   - Kernel parameter emulation (trit_kparams: kptr_restrict, etc.)
 *   - Restrictive mount options (noexec, nodev, nosuid)
 *   - SUID audit and privilege scanning
 *   - Ternary firewall (nftables-like packet filtering)
 *   - Minimal base enforcement (strip unneeded modules)
 *   - Pointer hiding, stack protection, ASLR emulation
 *
 * All hardening is user-space only — zero kernel modifications.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_HARDENING_H
#define TRIT_LINUX_HARDENING_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define THARD_MAX_PARAMS       16     /* Max kernel param emulations        */
#define THARD_MAX_MOUNTS       16     /* Max monitored mount points         */
#define THARD_MAX_FW_RULES     32     /* Max firewall rules                 */
#define THARD_MAX_AUDIT_ENTRIES 64    /* Max SUID audit entries             */
#define THARD_PARAM_KEY_LEN    32     /* Max param key length               */
#define THARD_PARAM_VAL_LEN    16     /* Max param value length             */
#define THARD_MOUNT_PATH_LEN   48     /* Max mount path length              */
#define THARD_FW_NAME_LEN      24     /* Max firewall rule name             */

/* Kernel parameter IDs (Arch-inspired) */
#define TKPARAM_KPTR_RESTRICT     0   /* Kernel pointer restriction         */
#define TKPARAM_DMESG_RESTRICT    1   /* dmesg restriction                  */
#define TKPARAM_PERF_RESTRICT     2   /* perf event restriction             */
#define TKPARAM_MMAP_MIN_ADDR     3   /* Min mmap address                   */
#define TKPARAM_RANDOMIZE_VA      4   /* ASLR analog                        */
#define TKPARAM_STACK_PROTECT     5   /* Stack protection level             */

/* Mount option flags */
#define TMOUNT_NOEXEC          (1 << 0)   /* No execution from mount       */
#define TMOUNT_NODEV           (1 << 1)   /* No device access              */
#define TMOUNT_NOSUID          (1 << 2)   /* No SUID execution             */
#define TMOUNT_READONLY        (1 << 3)   /* Read-only mount               */

/* Firewall actions */
#define TFW_ACTION_ACCEPT      TRIT_TRUE
#define TFW_ACTION_LOG         TRIT_UNKNOWN
#define TFW_ACTION_DROP        TRIT_FALSE

/* Firewall directions */
#define TFW_DIR_INBOUND        0
#define TFW_DIR_OUTBOUND       1
#define TFW_DIR_BOTH           2

/* Audit severity */
#define TAUDIT_SEV_INFO        0
#define TAUDIT_SEV_WARN        1
#define TAUDIT_SEV_CRIT        2

/* Error codes */
#define THARD_OK                 0
#define THARD_ERR_INIT          (-1)
#define THARD_ERR_FULL          (-2)
#define THARD_ERR_NOTFOUND      (-3)
#define THARD_ERR_DENIED        (-4)
#define THARD_ERR_VIOLATION     (-5)

/* ==== Types ============================================================= */

/**
 * @brief Emulated kernel parameter.
 */
typedef struct {
    char  key[THARD_PARAM_KEY_LEN];    /**< Parameter name                  */
    int   value;                       /**< Integer value                   */
    int   id;                          /**< Parameter ID (TKPARAM_*)        */
    int   active;                      /**< 1 = param is enforced           */
} thard_kparam_t;

/**
 * @brief Monitored mount point with restrictive options.
 */
typedef struct {
    char  path[THARD_MOUNT_PATH_LEN];  /**< Mount point path               */
    int   flags;                       /**< TMOUNT_* bitmask                */
    int   active;                      /**< 1 = mount is monitored          */
    int   violations;                  /**< Count of policy violations      */
} thard_mount_t;

/**
 * @brief Firewall rule for ternary packet filtering.
 */
typedef struct {
    char  name[THARD_FW_NAME_LEN];     /**< Rule name                      */
    int   direction;                   /**< TFW_DIR_*                       */
    trit  action;                      /**< TFW_ACTION_*                    */
    int   src_module;                  /**< Source module ID (-1 = any)      */
    int   dst_module;                  /**< Dest module ID (-1 = any)        */
    int   matches;                     /**< Number of times rule matched    */
    int   active;                      /**< 1 = rule is enforced            */
} thard_fw_rule_t;

/**
 * @brief SUID audit entry.
 */
typedef struct {
    int   module_id;                   /**< Module ID                       */
    int   has_suid;                    /**< 1 = has SUID-like escalation    */
    int   severity;                    /**< TAUDIT_SEV_*                    */
    trit  status;                      /**< +1=clean, 0=warning, -1=vuln    */
} thard_audit_entry_t;

/**
 * @brief Hardening framework state.
 */
typedef struct {
    /* Kernel params */
    thard_kparam_t     params[THARD_MAX_PARAMS];
    int                param_count;

    /* Mount restrictions */
    thard_mount_t      mounts[THARD_MAX_MOUNTS];
    int                mount_count;

    /* Firewall */
    thard_fw_rule_t    fw_rules[THARD_MAX_FW_RULES];
    int                fw_rule_count;
    int                fw_packets_accepted;
    int                fw_packets_dropped;
    int                fw_packets_logged;

    /* SUID audit */
    thard_audit_entry_t audit[THARD_MAX_AUDIT_ENTRIES];
    int                audit_count;
    int                suid_found;
    int                vulnerabilities;

    /* Overall status */
    trit  hardening_status;            /**< +1=hardened, 0=partial, -1=weak */
    int   initialized;
} thard_state_t;

/* ---- Inline implementations ---- */
/**
 * @file trit_hardening.c
 * @brief seT6 Trit Linux — Attack Surface Reduction & Hardening Implementation
 *
 * Implements kernel param emulation, restrictive mounts, ternary firewall,
 * SUID auditing, and hardening score computation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */


/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

static inline int thard_init(thard_state_t *hs) {
    if (!hs) return THARD_ERR_INIT;

    memset(hs, 0, sizeof(*hs));
    hs->hardening_status = TRIT_UNKNOWN;  /* Partial until fully configured */
    hs->initialized = 1;
    return THARD_OK;
}

/* ==================================================================== */
/*  Kernel Parameter Emulation                                          */
/* ==================================================================== */

static inline int thard_set_kparam(thard_state_t *hs, int param_id, int value) {
    if (!hs || !hs->initialized) return THARD_ERR_INIT;

    /* Find existing or add new */
    for (int i = 0; i < hs->param_count; i++) {
        if (hs->params[i].id == param_id) {
            hs->params[i].value = value;
            hs->params[i].active = 1;
            return THARD_OK;
        }
    }

    if (hs->param_count >= THARD_MAX_PARAMS) return THARD_ERR_FULL;

    thard_kparam_t *p = &hs->params[hs->param_count];
    memset(p, 0, sizeof(*p));
    p->id = param_id;
    p->value = value;
    p->active = 1;

    /* Set descriptive key name */
    switch (param_id) {
        case TKPARAM_KPTR_RESTRICT:  strncpy(p->key, "kptr_restrict", THARD_PARAM_KEY_LEN - 1); break;
        case TKPARAM_DMESG_RESTRICT: strncpy(p->key, "dmesg_restrict", THARD_PARAM_KEY_LEN - 1); break;
        case TKPARAM_PERF_RESTRICT:  strncpy(p->key, "perf_restrict", THARD_PARAM_KEY_LEN - 1); break;
        case TKPARAM_MMAP_MIN_ADDR:  strncpy(p->key, "mmap_min_addr", THARD_PARAM_KEY_LEN - 1); break;
        case TKPARAM_RANDOMIZE_VA:   strncpy(p->key, "randomize_va", THARD_PARAM_KEY_LEN - 1); break;
        case TKPARAM_STACK_PROTECT:  strncpy(p->key, "stack_protect", THARD_PARAM_KEY_LEN - 1); break;
        default: snprintf(p->key, THARD_PARAM_KEY_LEN, "param_%d", param_id); break;
    }

    hs->param_count++;
    return THARD_OK;
}

static inline int thard_get_kparam(const thard_state_t *hs, int param_id) {
    if (!hs || !hs->initialized) return -1;

    for (int i = 0; i < hs->param_count; i++) {
        if (hs->params[i].id == param_id && hs->params[i].active) {
            return hs->params[i].value;
        }
    }
    return -1;  /* Not found */
}

/* ==================================================================== */
/*  Restrictive Mount Options                                           */
/* ==================================================================== */

static inline int thard_mount_add(thard_state_t *hs, const char *path, int flags) {
    if (!hs || !hs->initialized || !path) return THARD_ERR_INIT;
    if (hs->mount_count >= THARD_MAX_MOUNTS) return THARD_ERR_FULL;

    thard_mount_t *m = &hs->mounts[hs->mount_count];
    memset(m, 0, sizeof(*m));

    strncpy(m->path, path, THARD_MOUNT_PATH_LEN - 1);
    m->flags = flags;
    m->active = 1;

    hs->mount_count++;
    return THARD_OK;
}

static inline int thard_mount_check(thard_state_t *hs, const char *path, int required_perms) {
    if (!hs || !hs->initialized || !path) return THARD_ERR_INIT;

    for (int i = 0; i < hs->mount_count; i++) {
        if (!hs->mounts[i].active) continue;
        if (strncmp(hs->mounts[i].path, path, THARD_MOUNT_PATH_LEN) != 0) continue;

        int flags = hs->mounts[i].flags;

        /* Check NOEXEC: if mount is noexec and we want exec, deny */
        if ((flags & TMOUNT_NOEXEC) && (required_perms & TMOUNT_NOEXEC)) {
            hs->mounts[i].violations++;
            return THARD_ERR_DENIED;
        }

        /* Check NOSUID: if mount is nosuid and we want suid, deny */
        if ((flags & TMOUNT_NOSUID) && (required_perms & TMOUNT_NOSUID)) {
            hs->mounts[i].violations++;
            return THARD_ERR_DENIED;
        }

        /* Check NODEV: if mount is nodev and we want dev, deny */
        if ((flags & TMOUNT_NODEV) && (required_perms & TMOUNT_NODEV)) {
            hs->mounts[i].violations++;
            return THARD_ERR_DENIED;
        }

        /* Check READONLY: if mount is readonly and we want write (nosuid reuse) */
        if ((flags & TMOUNT_READONLY) && (required_perms & TMOUNT_READONLY)) {
            hs->mounts[i].violations++;
            return THARD_ERR_DENIED;
        }

        return THARD_OK;  /* Allowed */
    }

    return THARD_ERR_NOTFOUND;  /* Mount not monitored */
}

/* ==================================================================== */
/*  Ternary Firewall (nftables-like)                                    */
/* ==================================================================== */

static inline int thard_fw_add_rule(thard_state_t *hs, const char *name,
                      int direction, trit action,
                      int src_module, int dst_module) {
    if (!hs || !hs->initialized || !name) return THARD_ERR_INIT;
    if (hs->fw_rule_count >= THARD_MAX_FW_RULES) return THARD_ERR_FULL;

    thard_fw_rule_t *r = &hs->fw_rules[hs->fw_rule_count];
    memset(r, 0, sizeof(*r));

    strncpy(r->name, name, THARD_FW_NAME_LEN - 1);
    r->direction = direction;
    r->action = action;
    r->src_module = src_module;
    r->dst_module = dst_module;
    r->active = 1;

    hs->fw_rule_count++;
    return THARD_OK;
}

static inline trit thard_fw_check(thard_state_t *hs, int src_module, int dst_module,
                    int direction) {
    if (!hs || !hs->initialized) return TRIT_FALSE;

    /* Default policy: accept if no rules match */
    trit result = TRIT_TRUE;

    for (int i = 0; i < hs->fw_rule_count; i++) {
        thard_fw_rule_t *r = &hs->fw_rules[i];
        if (!r->active) continue;

        /* Direction match */
        if (r->direction != TFW_DIR_BOTH && r->direction != direction) continue;

        /* Source match (-1 = wildcard) */
        if (r->src_module != -1 && r->src_module != src_module) continue;

        /* Dest match (-1 = wildcard) */
        if (r->dst_module != -1 && r->dst_module != dst_module) continue;

        /* Rule matches — apply action */
        r->matches++;
        result = r->action;

        /* Track stats */
        if (result == TFW_ACTION_DROP) {
            hs->fw_packets_dropped++;
        } else if (result == TFW_ACTION_LOG) {
            hs->fw_packets_logged++;
        } else {
            hs->fw_packets_accepted++;
        }

        /* First match wins (like iptables) */
        return result;
    }

    /* No rules matched — default accept */
    hs->fw_packets_accepted++;
    return TRIT_TRUE;
}

/* ==================================================================== */
/*  SUID Audit                                                          */
/* ==================================================================== */

static inline int thard_audit_module(thard_state_t *hs, int module_id, int has_suid) {
    if (!hs || !hs->initialized) return THARD_ERR_INIT;
    if (hs->audit_count >= THARD_MAX_AUDIT_ENTRIES) return THARD_ERR_FULL;

    thard_audit_entry_t *ae = &hs->audit[hs->audit_count];
    memset(ae, 0, sizeof(*ae));

    ae->module_id = module_id;
    ae->has_suid = has_suid;

    if (has_suid) {
        ae->severity = TAUDIT_SEV_CRIT;
        ae->status = TRIT_FALSE;  /* Vulnerable */
        hs->suid_found++;
    } else {
        ae->severity = TAUDIT_SEV_INFO;
        ae->status = TRIT_TRUE;   /* Clean */
    }

    hs->audit_count++;
    return THARD_OK;
}

static inline int thard_audit_scan(thard_state_t *hs) {
    if (!hs || !hs->initialized) return THARD_ERR_INIT;

    hs->vulnerabilities = 0;
    for (int i = 0; i < hs->audit_count; i++) {
        if (hs->audit[i].has_suid) {
            hs->vulnerabilities++;
        }
    }
    return hs->vulnerabilities;
}

/* ==================================================================== */
/*  Hardening Score                                                     */
/* ==================================================================== */

static inline int thard_compute_score(thard_state_t *hs) {
    if (!hs || !hs->initialized) return 0;

    int score = 0;
    int max_score = 0;

    /* Kernel params configured: +10 each */
    max_score += 60;
    score += hs->param_count * 10;
    if (score > 60) score = 60;

    /* Mounts hardened: +5 each */
    max_score += 40;
    for (int i = 0; i < hs->mount_count; i++) {
        if (hs->mounts[i].active) score += 5;
    }
    if (score > 100) score = 100;

    /* Firewall rules: +3 each */
    max_score += 30;
    score += hs->fw_rule_count * 3;
    if (score > 130) score = 130;

    /* No SUID found: +20 bonus */
    max_score += 20;
    if (hs->suid_found == 0 && hs->audit_count > 0) {
        score += 20;
    }

    /* Update status */
    if (score >= max_score * 8 / 10) {
        hs->hardening_status = TRIT_TRUE;      /* Fully hardened */
    } else if (score >= max_score * 4 / 10) {
        hs->hardening_status = TRIT_UNKNOWN;   /* Partially hardened */
    } else {
        hs->hardening_status = TRIT_FALSE;     /* Weak */
    }

    return score;
}

static inline int thard_fw_dropped(const thard_state_t *hs) {
    if (!hs) return 0;
    return hs->fw_packets_dropped;
}

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_HARDENING_H */
