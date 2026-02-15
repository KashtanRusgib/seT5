/**
 * @file trit_security.h
 * @brief Trit Linux — Security and Auditing Enhancements Header
 *
 * Provides trit-state audit logging, ternary SELinux-like policy
 * enforcement using priority queues, and side-channel resistance
 * monitoring leveraging DLFET-RM low-EMI characteristics.
 *
 * Enhancement 6 from LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *   "Security and Auditing Enhancements"
 *
 * Key features:
 *   - T-Audit: syscall trit-state logging with "Unknown" escalation detection
 *   - T-Policy: ternary SELinux analog with priority-queue enforcement
 *   - T-Sandbox: enhanced process isolation with capability narrowing
 *   - Side-channel monitor: tracks EMI and timing variance
 *   - Fault injection detection using temporal logic (TTL)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_SECURITY_H
#define TRIT_LINUX_TRIT_SECURITY_H

#include "set6/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TSEC_MAX_LOG_ENTRIES  128   /* Max audit log entries                */
#define TSEC_MAX_POLICIES    32    /* Max security policies                */
#define TSEC_MAX_SANDBOXES   8     /* Max active sandboxes                 */
#define TSEC_SUBJECT_LEN     24    /* Max subject name length              */
#define TSEC_OBJECT_LEN      24    /* Max object name length               */

/* Audit event types */
#define TSEC_EVT_SYSCALL     1     /* System call audit                    */
#define TSEC_EVT_IPC         2     /* IPC message audit                    */
#define TSEC_EVT_MEM         3     /* Memory access audit                  */
#define TSEC_EVT_NET         4     /* Network activity audit               */
#define TSEC_EVT_FILE        5     /* File access audit                    */
#define TSEC_EVT_POLICY      6     /* Policy violation audit               */
#define TSEC_EVT_ESCALATION  7     /* Unknown → True escalation attempt    */

/* Error codes */
#define TSEC_OK              0
#define TSEC_ERR_INIT       (-1)
#define TSEC_ERR_FULL       (-2)
#define TSEC_ERR_DENIED     (-3)
#define TSEC_ERR_NOTFOUND   (-4)
#define TSEC_ERR_VIOLATION  (-5)

/* Policy actions (ternary) */
#define TSEC_ALLOW           TRIT_TRUE     /* +1: permit access            */
#define TSEC_AUDIT           TRIT_UNKNOWN  /*  0: log and permit           */
#define TSEC_DENY            TRIT_FALSE    /* -1: deny access              */

/* Permission bits */
#define TSEC_PERM_READ       (1 << 0)
#define TSEC_PERM_WRITE      (1 << 1)
#define TSEC_PERM_EXEC       (1 << 2)
#define TSEC_PERM_IPC        (1 << 3)
#define TSEC_PERM_NET        (1 << 4)

/* ==== Types ============================================================= */

/**
 * @brief Audit log entry.
 *
 * Records a security-relevant event with trit-state outcome:
 *   +1 (True)    = action succeeded
 *    0 (Unknown) = action in indeterminate state (potential threat)
 *   -1 (False)   = action was denied
 */
typedef struct {
    int  event_type;             /**< Event type (TSEC_EVT_*)              */
    int  timestamp;              /**< Monotonic tick counter               */
    char subject[TSEC_SUBJECT_LEN]; /**< Subject (process/user)           */
    char object[TSEC_OBJECT_LEN];  /**< Target object (file/resource)     */
    int  permissions;            /**< Requested permissions bitmask        */
    trit outcome;                /**< T=success, U=unknown, F=denied       */
    int  escalation;             /**< 1 if Unknown→True escalation detected*/
} tsec_audit_entry_t;

/**
 * @brief Security policy rule (ternary SELinux analog).
 *
 * Defines access control for a subject-object pair with trit action:
 *   +1 = allow (high-priority pass)
 *    0 = audit (log and permit; stateful inspection)
 *   -1 = deny (block access)
 */
typedef struct {
    char subject[TSEC_SUBJECT_LEN]; /**< Process/role name                */
    char object[TSEC_OBJECT_LEN];  /**< Resource name                     */
    int  permissions;            /**< Permission mask to control            */
    trit action;                 /**< +1=allow, 0=audit, -1=deny           */
    int  priority;               /**< Evaluation priority (higher = first) */
    int  match_count;            /**< Times this policy was triggered      */
    int  active;                 /**< 1 = rule enabled                     */
} tsec_policy_t;

/**
 * @brief Sandbox descriptor for process isolation.
 *
 * Provides enhanced isolation via capability narrowing:
 * each sandbox has a restricted set of allowed permissions
 * and a maximum capability width.
 */
typedef struct {
    int  id;                     /**< Sandbox ID                           */
    char name[TSEC_SUBJECT_LEN]; /**< Sandbox name                        */
    int  allowed_perms;          /**< Bitmask of allowed permissions       */
    int  max_memory_pages;       /**< Maximum memory pages allowed         */
    int  max_ipc_channels;       /**< Maximum IPC channels allowed         */
    trit trust_level;            /**< T=trusted, U=semi-trusted, F=untrusted*/
    int  active;                 /**< 1 = sandbox active                   */
    int  violations;             /**< Cumulative policy violations         */
} tsec_sandbox_t;

/**
 * @brief Side-channel monitoring state.
 *
 * Tracks timing variance and EMI indicators that might suggest
 * side-channel attacks. Leverages DLFET-RM low-EMI properties.
 */
typedef struct {
    int  timing_samples;         /**< Number of timing samples collected   */
    int  timing_variance;        /**< Variance × 100 of execution times   */
    int  emi_alerts;             /**< EMI anomaly alerts                   */
    int  fault_injections;       /**< Detected fault injection attempts    */
    trit channel_status;         /**< T=secure, U=suspicious, F=compromised*/
} tsec_sidechannel_t;

/**
 * @brief Security module master state.
 *
 * Integrates audit logging, policy enforcement, sandboxing,
 * and side-channel monitoring.
 */
typedef struct {
    /* Audit log (circular buffer) */
    tsec_audit_entry_t log[TSEC_MAX_LOG_ENTRIES];
    int                log_head;
    int                log_tail;
    int                log_count;     /**< Current entries in log          */
    int                log_total;     /**< Total events logged (wraps)     */

    /* Security policies */
    tsec_policy_t      policies[TSEC_MAX_POLICIES];
    int                policy_count;

    /* Sandboxes */
    tsec_sandbox_t     sandboxes[TSEC_MAX_SANDBOXES];
    int                sandbox_count;

    /* Side-channel monitor */
    tsec_sidechannel_t sidechannel;

    /* Global state */
    int                initialized;
    int                total_denials;    /**< Total access denials         */
    int                total_escalations;/**< Total escalation attempts    */
    int                clock_tick;       /**< Monotonic audit clock         */
} tsec_state_t;

/* ==== Initialization ==================================================== */

/** Initialize the security module */
int tsec_init(tsec_state_t *sec);

/* ==== Audit Logging ===================================================== */

/** Log a security event */
int tsec_audit_log(tsec_state_t *sec, int event_type,
                   const char *subject, const char *object,
                   int permissions, trit outcome);

/** Get the most recent N log entries */
int tsec_audit_recent(const tsec_state_t *sec,
                      tsec_audit_entry_t *out, int max_entries);

/** Count log entries matching a specific event type */
int tsec_audit_count_type(const tsec_state_t *sec, int event_type);

/** Count escalation events (Unknown → True transitions) */
int tsec_audit_count_escalations(const tsec_state_t *sec);

/* ==== Policy Enforcement ================================================= */

/** Add a security policy rule */
int tsec_policy_add(tsec_state_t *sec, const char *subject, const char *object,
                    int permissions, trit action, int priority);

/** Evaluate access: checks all policies and returns trit action */
trit tsec_policy_evaluate(tsec_state_t *sec, const char *subject,
                          const char *object, int permissions);

/** Enforce access: evaluate + log + deny if policy says so */
int tsec_enforce(tsec_state_t *sec, const char *subject,
                 const char *object, int permissions);

/* ==== Sandboxing ========================================================= */

/** Create a new sandbox */
int tsec_sandbox_create(tsec_state_t *sec, const char *name,
                        int allowed_perms, trit trust_level);

/** Check if an operation is allowed in a sandbox */
int tsec_sandbox_check(const tsec_state_t *sec, int sandbox_id, int permissions);

/** Destroy a sandbox */
int tsec_sandbox_destroy(tsec_state_t *sec, int sandbox_id);

/* ==== Side-Channel Monitoring ============================================ */

/** Record a timing sample (for variance analysis) */
int tsec_timing_sample(tsec_state_t *sec, int execution_time);

/** Report EMI anomaly */
int tsec_emi_alert(tsec_state_t *sec);

/** Report fault injection detection */
int tsec_fault_detected(tsec_state_t *sec);

/** Get side-channel status */
trit tsec_sidechannel_status(const tsec_state_t *sec);

/* ==== Statistics ========================================================= */

/** Get security statistics */
void tsec_stats(const tsec_state_t *sec,
                int *total_events, int *denials, int *escalations,
                int *active_sandboxes);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_SECURITY_H */
