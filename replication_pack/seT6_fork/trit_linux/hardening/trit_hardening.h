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

#include "set6/trit.h"

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

/* ==== API =============================================================== */

/** Initialize the hardening framework. */
int thard_init(thard_state_t *hs);

/** Set an emulated kernel parameter. */
int thard_set_kparam(thard_state_t *hs, int param_id, int value);

/** Get an emulated kernel parameter value. */
int thard_get_kparam(const thard_state_t *hs, int param_id);

/** Add a mount point with restrictive options. */
int thard_mount_add(thard_state_t *hs, const char *path, int flags);

/** Check if an operation is allowed on a mount point. */
int thard_mount_check(thard_state_t *hs, const char *path, int required_perms);

/** Add a firewall rule. */
int thard_fw_add_rule(thard_state_t *hs, const char *name,
                      int direction, trit action,
                      int src_module, int dst_module);

/** Check firewall against a packet (src→dst). */
trit thard_fw_check(thard_state_t *hs, int src_module, int dst_module,
                    int direction);

/** Audit a module for SUID-like escalation. */
int thard_audit_module(thard_state_t *hs, int module_id, int has_suid);

/** Run full SUID scan across all registered audits. */
int thard_audit_scan(thard_state_t *hs);

/** Compute overall hardening score. */
int thard_compute_score(thard_state_t *hs);

/** Get firewall stats. */
int thard_fw_dropped(const thard_state_t *hs);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_HARDENING_H */
