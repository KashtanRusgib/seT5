/**
 * @file trit_hardening.h
 * @brief seT6 — Attack Surface Reduction & Hardening (inline implementation)
 *
 * Provides kernel parameter emulation, restrictive mount options,
 * ternary firewall rules, SUID audit/vulnerability scanning,
 * and hardening score computation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_HARDENING_H
#define TRIT_HARDENING_H

#include <string.h>
#include <stdint.h>
#include "set5/trit.h"

/* ======================================================================== */
/*  Error Codes                                                             */
/* ======================================================================== */

#define THARD_OK            0
#define THARD_ERR_INIT     -1
#define THARD_ERR_DENIED   -2
#define THARD_ERR_NOTFOUND -3

/* ======================================================================== */
/*  Kernel Parameter IDs                                                    */
/* ======================================================================== */

#define TKPARAM_KPTR_RESTRICT   0
#define TKPARAM_DMESG_RESTRICT  1
#define TKPARAM_PERF_RESTRICT   2
#define TKPARAM_MMAP_MIN_ADDR   3
#define TKPARAM_RANDOMIZE_VA    4
#define TKPARAM_STACK_PROTECT   5

/* ======================================================================== */
/*  Mount Flags (bitmask)                                                   */
/* ======================================================================== */

#define TMOUNT_NOEXEC    1
#define TMOUNT_NOSUID    2
#define TMOUNT_NODEV     4
#define TMOUNT_READONLY  8

/* ======================================================================== */
/*  Firewall Directions                                                     */
/* ======================================================================== */

#define TFW_DIR_OUTBOUND  0
#define TFW_DIR_INBOUND   1
#define TFW_DIR_BOTH      2

/* ======================================================================== */
/*  Firewall Actions                                                        */
/* ======================================================================== */

#define TFW_ACTION_ACCEPT  1   /* same numeric value as TRIT_TRUE */
#define TFW_ACTION_DROP    2
#define TFW_ACTION_LOG     3

/* ======================================================================== */
/*  Audit Severity                                                          */
/* ======================================================================== */

#define TAUDIT_SEV_CRIT  1

/* ======================================================================== */
/*  Array Limits                                                            */
/* ======================================================================== */

#define THARD_MAX_PARAMS  16
#define THARD_MAX_MOUNTS  16
#define THARD_MAX_FW      16
#define THARD_MAX_AUDIT   16

/* ======================================================================== */
/*  Internal Structs                                                        */
/* ======================================================================== */

typedef struct {
    int id;
    int value;
} thard_kparam_t;

typedef struct {
    char path[64];
    int  flags;
    int  violations;
} thard_mount_t;

typedef struct {
    char name[32];
    int  direction;
    int  action;
    int  src;
    int  dst;
} thard_fw_rule_t;

typedef struct {
    trit status;
    int  severity;
} thard_audit_entry_t;

/* ======================================================================== */
/*  Main State                                                              */
/* ======================================================================== */

typedef struct {
    trit hardening_status;
    int  param_count;
    int  mount_count;
    int  fw_rule_count;
    int  fw_packets_accepted;
    int  fw_packets_dropped;
    int  fw_packets_logged;
    int  suid_found;
    int  vulnerabilities;
    int  audit_count;

    thard_kparam_t      params[THARD_MAX_PARAMS];
    thard_mount_t       mounts[THARD_MAX_MOUNTS];
    thard_fw_rule_t     fw_rules[THARD_MAX_FW];
    thard_audit_entry_t audit[THARD_MAX_AUDIT];
} thard_state_t;

/* ======================================================================== */
/*  Initialization                                                          */
/* ======================================================================== */

static inline int thard_init(thard_state_t *hs) {
    if (!hs) return THARD_ERR_INIT;
    memset(hs, 0, sizeof(*hs));
    hs->hardening_status = TRIT_UNKNOWN;
    return THARD_OK;
}

/* ======================================================================== */
/*  Kernel Parameter Emulation                                              */
/* ======================================================================== */

static inline int thard_set_kparam(thard_state_t *hs, int param_id, int value) {
    /* Override existing param if found */
    for (int i = 0; i < hs->param_count; i++) {
        if (hs->params[i].id == param_id) {
            hs->params[i].value = value;
            return THARD_OK;
        }
    }
    /* Add new param */
    if (hs->param_count >= THARD_MAX_PARAMS) return THARD_ERR_INIT;
    hs->params[hs->param_count].id    = param_id;
    hs->params[hs->param_count].value = value;
    hs->param_count++;
    return THARD_OK;
}

static inline int thard_get_kparam(thard_state_t *hs, int param_id) {
    for (int i = 0; i < hs->param_count; i++) {
        if (hs->params[i].id == param_id)
            return hs->params[i].value;
    }
    return -1;
}

/* ======================================================================== */
/*  Restrictive Mounts                                                      */
/* ======================================================================== */

static inline int thard_mount_add(thard_state_t *hs, const char *path, int flags) {
    if (hs->mount_count >= THARD_MAX_MOUNTS) return THARD_ERR_INIT;
    thard_mount_t *m = &hs->mounts[hs->mount_count];
    strncpy(m->path, path, sizeof(m->path) - 1);
    m->path[sizeof(m->path) - 1] = '\0';
    m->flags      = flags;
    m->violations = 0;
    hs->mount_count++;
    return THARD_OK;
}

static inline int thard_mount_check(thard_state_t *hs, const char *path, int flag) {
    for (int i = 0; i < hs->mount_count; i++) {
        if (strcmp(hs->mounts[i].path, path) == 0) {
            if (hs->mounts[i].flags & flag) {
                hs->mounts[i].violations++;
                return THARD_ERR_DENIED;
            }
            return THARD_OK;
        }
    }
    return THARD_ERR_NOTFOUND;
}

/* ======================================================================== */
/*  Ternary Firewall                                                        */
/* ======================================================================== */

static inline int thard_fw_add_rule(thard_state_t *hs, const char *name,
                                    int direction, int action,
                                    int src, int dst) {
    if (hs->fw_rule_count >= THARD_MAX_FW) return THARD_ERR_INIT;
    thard_fw_rule_t *r = &hs->fw_rules[hs->fw_rule_count];
    strncpy(r->name, name, sizeof(r->name) - 1);
    r->name[sizeof(r->name) - 1] = '\0';
    r->direction = direction;
    r->action    = action;
    r->src       = src;
    r->dst       = dst;
    hs->fw_rule_count++;
    return THARD_OK;
}

static inline int thard_fw_check(thard_state_t *hs, int src, int dst, int direction) {
    for (int i = 0; i < hs->fw_rule_count; i++) {
        thard_fw_rule_t *r = &hs->fw_rules[i];
        int src_match = (r->src == -1 || r->src == src);
        int dst_match = (r->dst == -1 || r->dst == dst);
        int dir_match = (r->direction == TFW_DIR_BOTH || r->direction == direction);
        if (src_match && dst_match && dir_match) {
            if (r->action == TFW_ACTION_ACCEPT) hs->fw_packets_accepted++;
            else if (r->action == TFW_ACTION_DROP) hs->fw_packets_dropped++;
            else if (r->action == TFW_ACTION_LOG) hs->fw_packets_logged++;
            return r->action;
        }
    }
    /* Default policy: accept */
    hs->fw_packets_accepted++;
    return TRIT_TRUE;
}

static inline int thard_fw_dropped(thard_state_t *hs) {
    return hs->fw_packets_dropped;
}

/* ======================================================================== */
/*  SUID Audit & Vulnerability Scanning                                     */
/* ======================================================================== */

static inline int thard_audit_module(thard_state_t *hs, int module_id, int has_suid) {
    if (module_id < 0 || module_id >= THARD_MAX_AUDIT) return THARD_ERR_INIT;
    if (module_id >= hs->audit_count)
        hs->audit_count = module_id + 1;
    if (has_suid) {
        hs->audit[module_id].status   = TRIT_FALSE;
        hs->audit[module_id].severity = TAUDIT_SEV_CRIT;
        hs->suid_found++;
    } else {
        hs->audit[module_id].status   = TRIT_TRUE;
        hs->audit[module_id].severity = 0;
    }
    return THARD_OK;
}

static inline int thard_audit_scan(thard_state_t *hs) {
    int count = 0;
    for (int i = 0; i < hs->audit_count; i++) {
        if (hs->audit[i].status == TRIT_FALSE)
            count++;
    }
    hs->vulnerabilities = count;
    return count;
}

/* ======================================================================== */
/*  Hardening Score Computation                                             */
/* ======================================================================== */

static inline int thard_compute_score(thard_state_t *hs) {
    int score = 0;

    score += hs->param_count   * 10;  /* 10 pts per kernel param  */
    score += hs->mount_count   *  5;  /*  5 pts per mount         */
    score += hs->fw_rule_count *  3;  /*  3 pts per firewall rule */

    /* 20-point bonus if all audited modules are clean (no SUID) */
    if (hs->audit_count > 0) {
        int all_clean = 1;
        for (int i = 0; i < hs->audit_count; i++) {
            if (hs->audit[i].status != TRIT_TRUE) {
                all_clean = 0;
                break;
            }
        }
        if (all_clean) score += 20;
    }

    if (score >= 100)
        hs->hardening_status = TRIT_TRUE;

    return score;
}

#endif /* TRIT_HARDENING_H */
