/**
 * @file trit_security.c
 * @brief Trit Linux — Security and Auditing Implementation
 *
 * Implements T-Audit logging, T-Policy enforcement with trit-state
 * access control, T-Sandbox isolation, and side-channel monitoring.
 *
 * Enhancement 6: "Security and Auditing Enhancements"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "trit_security.h"

/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

int tsec_init(tsec_state_t *sec) {
    if (!sec) return TSEC_ERR_INIT;

    memset(sec, 0, sizeof(*sec));

    /* Initialize side-channel monitor to secure state */
    sec->sidechannel.channel_status = TRIT_TRUE;

    /* Mark all sandboxes as inactive */
    for (int i = 0; i < TSEC_MAX_SANDBOXES; i++) {
        sec->sandboxes[i].id = -1;
        sec->sandboxes[i].active = 0;
    }

    sec->initialized = 1;
    return TSEC_OK;
}

/* ==================================================================== */
/*  Audit Logging — Circular buffer of security events                  */
/* ==================================================================== */

int tsec_audit_log(tsec_state_t *sec, int event_type,
                   const char *subject, const char *object,
                   int permissions, trit outcome) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;

    /*
     * Write audit entry into circular buffer. If full, overwrite
     * the oldest entry (ring buffer semantics).
     */
    tsec_audit_entry_t *entry = &sec->log[sec->log_tail];
    memset(entry, 0, sizeof(*entry));

    entry->event_type = event_type;
    entry->timestamp = sec->clock_tick++;
    if (subject) strncpy(entry->subject, subject, TSEC_SUBJECT_LEN - 1);
    if (object)  strncpy(entry->object, object, TSEC_OBJECT_LEN - 1);
    entry->permissions = permissions;
    entry->outcome = outcome;

    /*
     * Detect "Unknown" escalation: any audit event with Unknown outcome
     * is flagged as a potential escalation attempt. In a real system,
     * this detects privilege escalation through indeterminate states.
     */
    if (outcome == TRIT_UNKNOWN && event_type == TSEC_EVT_ESCALATION) {
        entry->escalation = 1;
        sec->total_escalations++;
    }

    /* Track denials */
    if (outcome == TRIT_FALSE) {
        sec->total_denials++;
    }

    /* Advance circular buffer */
    sec->log_tail = (sec->log_tail + 1) % TSEC_MAX_LOG_ENTRIES;
    if (sec->log_count < TSEC_MAX_LOG_ENTRIES) {
        sec->log_count++;
    } else {
        /* Buffer wrapped — advance head to drop oldest */
        sec->log_head = (sec->log_head + 1) % TSEC_MAX_LOG_ENTRIES;
    }
    sec->log_total++;

    return TSEC_OK;
}

int tsec_audit_recent(const tsec_state_t *sec,
                      tsec_audit_entry_t *out, int max_entries) {
    if (!sec || !out || !sec->initialized) return TSEC_ERR_INIT;

    int count = (max_entries < sec->log_count) ? max_entries : sec->log_count;

    /*
     * Read the most recent entries from the circular buffer.
     * Walk backwards from log_tail.
     */
    for (int i = 0; i < count; i++) {
        int idx = (sec->log_tail - 1 - i + TSEC_MAX_LOG_ENTRIES) % TSEC_MAX_LOG_ENTRIES;
        out[i] = sec->log[idx];
    }

    return count;
}

int tsec_audit_count_type(const tsec_state_t *sec, int event_type) {
    if (!sec || !sec->initialized) return 0;

    int count = 0;
    for (int i = 0; i < sec->log_count; i++) {
        int idx = (sec->log_head + i) % TSEC_MAX_LOG_ENTRIES;
        if (sec->log[idx].event_type == event_type) count++;
    }

    return count;
}

int tsec_audit_count_escalations(const tsec_state_t *sec) {
    if (!sec) return 0;
    return sec->total_escalations;
}

/* ==================================================================== */
/*  Policy Enforcement — Ternary SELinux analog                         */
/* ==================================================================== */

int tsec_policy_add(tsec_state_t *sec, const char *subject, const char *object,
                    int permissions, trit action, int priority) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;
    if (sec->policy_count >= TSEC_MAX_POLICIES) return TSEC_ERR_FULL;

    tsec_policy_t *pol = &sec->policies[sec->policy_count];
    memset(pol, 0, sizeof(*pol));

    if (subject) strncpy(pol->subject, subject, TSEC_SUBJECT_LEN - 1);
    if (object)  strncpy(pol->object, object, TSEC_OBJECT_LEN - 1);
    pol->permissions = permissions;
    pol->action = action;
    pol->priority = priority;
    pol->active = 1;

    sec->policy_count++;
    return TSEC_OK;
}

trit tsec_policy_evaluate(tsec_state_t *sec, const char *subject,
                          const char *object, int permissions) {
    if (!sec || !sec->initialized) return TRIT_TRUE; /* Default: allow */

    /*
     * Evaluate all active policies in priority order (highest first).
     * Find the highest-priority matching rule and return its action.
     *
     * Subject/object matching: empty string in policy = wildcard.
     * Permission matching: bitwise AND (any overlap matches).
     */
    int best_priority = -1;
    trit best_action = TRIT_TRUE; /* Default policy: allow */

    for (int i = 0; i < sec->policy_count; i++) {
        tsec_policy_t *pol = &sec->policies[i];
        if (!pol->active) continue;

        /* Check subject match (empty = wildcard) */
        if (pol->subject[0] != '\0' && subject &&
            strcmp(pol->subject, subject) != 0) {
            continue;
        }

        /* Check object match (empty = wildcard) */
        if (pol->object[0] != '\0' && object &&
            strcmp(pol->object, object) != 0) {
            continue;
        }

        /* Check permission overlap */
        if ((pol->permissions & permissions) == 0) continue;

        /* Higher priority wins */
        if (pol->priority > best_priority) {
            best_priority = pol->priority;
            best_action = pol->action;
            pol->match_count++;
        }
    }

    return best_action;
}

int tsec_enforce(tsec_state_t *sec, const char *subject,
                 const char *object, int permissions) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;

    /* Evaluate policy */
    trit action = tsec_policy_evaluate(sec, subject, object, permissions);

    /* Log the event */
    int evt_type = TSEC_EVT_POLICY;
    tsec_audit_log(sec, evt_type, subject, object, permissions, action);

    /* Deny if action is False */
    if (action == TRIT_FALSE) {
        return TSEC_ERR_DENIED;
    }

    /* Audit (log only) if action is Unknown — still allow */
    return TSEC_OK;
}

/* ==================================================================== */
/*  Sandboxing — Capability Narrowing                                   */
/* ==================================================================== */

int tsec_sandbox_create(tsec_state_t *sec, const char *name,
                        int allowed_perms, trit trust_level) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;
    if (sec->sandbox_count >= TSEC_MAX_SANDBOXES) return TSEC_ERR_FULL;

    /* Find a free sandbox slot */
    for (int i = 0; i < TSEC_MAX_SANDBOXES; i++) {
        if (!sec->sandboxes[i].active) {
            tsec_sandbox_t *sb = &sec->sandboxes[i];
            memset(sb, 0, sizeof(*sb));
            sb->id = i;
            if (name) strncpy(sb->name, name, TSEC_SUBJECT_LEN - 1);
            sb->allowed_perms = allowed_perms;
            sb->trust_level = trust_level;
            sb->max_memory_pages = 64;  /* Default: 64 pages */
            sb->max_ipc_channels = 4;   /* Default: 4 IPC channels */
            sb->active = 1;
            sec->sandbox_count++;
            return i; /* Return sandbox ID */
        }
    }

    return TSEC_ERR_FULL;
}

int tsec_sandbox_check(const tsec_state_t *sec, int sandbox_id, int permissions) {
    if (!sec || sandbox_id < 0 || sandbox_id >= TSEC_MAX_SANDBOXES)
        return TSEC_ERR_NOTFOUND;

    const tsec_sandbox_t *sb = &sec->sandboxes[sandbox_id];
    if (!sb->active) return TSEC_ERR_NOTFOUND;

    /*
     * Check if the requested permissions are within the sandbox's
     * allowed permission set. Uses bitwise AND — all requested
     * permissions must be in the allowed set.
     */
    if ((permissions & sb->allowed_perms) != permissions) {
        return TSEC_ERR_DENIED; /* Operation not allowed in sandbox */
    }

    return TSEC_OK;
}

int tsec_sandbox_destroy(tsec_state_t *sec, int sandbox_id) {
    if (!sec || sandbox_id < 0 || sandbox_id >= TSEC_MAX_SANDBOXES)
        return TSEC_ERR_NOTFOUND;

    if (!sec->sandboxes[sandbox_id].active) return TSEC_ERR_NOTFOUND;

    sec->sandboxes[sandbox_id].active = 0;
    sec->sandboxes[sandbox_id].id = -1;
    sec->sandbox_count--;

    return TSEC_OK;
}

/* ==================================================================== */
/*  Side-Channel Monitoring                                             */
/* ==================================================================== */

int tsec_timing_sample(tsec_state_t *sec, int execution_time) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;

    sec->sidechannel.timing_samples++;

    /*
     * Simple variance tracking: accumulate squared deviation from
     * a fixed expected timing. If variance exceeds threshold,
     * flag channel as suspicious.
     *
     * Expected execution time: assume ~100 units baseline.
     */
    int deviation = execution_time - 100;
    int sq_dev = deviation * deviation;

    /* Running variance approximation (exponential moving average) */
    sec->sidechannel.timing_variance =
        (sec->sidechannel.timing_variance * 7 + sq_dev * 100) / 8;

    /* Threshold: >5000 variance → suspicious */
    if (sec->sidechannel.timing_variance > 5000) {
        sec->sidechannel.channel_status = TRIT_UNKNOWN; /* Suspicious */
    }

    return TSEC_OK;
}

int tsec_emi_alert(tsec_state_t *sec) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;

    sec->sidechannel.emi_alerts++;

    /* After 3 EMI alerts, mark channel as compromised */
    if (sec->sidechannel.emi_alerts >= 3) {
        sec->sidechannel.channel_status = TRIT_FALSE;
    }

    tsec_audit_log(sec, TSEC_EVT_MEM, "monitor", "emi_sensor",
                   0, TRIT_UNKNOWN);

    return TSEC_OK;
}

int tsec_fault_detected(tsec_state_t *sec) {
    if (!sec || !sec->initialized) return TSEC_ERR_INIT;

    sec->sidechannel.fault_injections++;

    /* Any fault injection immediately compromises the channel */
    sec->sidechannel.channel_status = TRIT_FALSE;

    tsec_audit_log(sec, TSEC_EVT_ESCALATION, "unknown", "fault_injector",
                   TSEC_PERM_EXEC, TRIT_UNKNOWN);

    return TSEC_OK;
}

trit tsec_sidechannel_status(const tsec_state_t *sec) {
    if (!sec) return TRIT_FALSE;
    return sec->sidechannel.channel_status;
}

/* ==================================================================== */
/*  Statistics                                                          */
/* ==================================================================== */

void tsec_stats(const tsec_state_t *sec,
                int *total_events, int *denials, int *escalations,
                int *active_sandboxes) {
    if (!sec) return;
    if (total_events)     *total_events     = sec->log_total;
    if (denials)          *denials           = sec->total_denials;
    if (escalations)      *escalations       = sec->total_escalations;
    if (active_sandboxes) *active_sandboxes  = sec->sandbox_count;
}
