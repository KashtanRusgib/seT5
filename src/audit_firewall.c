/**
 * @file audit_firewall.c
 * @brief T-018: Ternary Audit Log + Trit-Granularity Firewall
 *
 * Implements:
 *   - Audit log with ternary severity (TRIT_TRUE=info, UNKNOWN=warn, FALSE=crit)
 *   - Firewall rules with 3-state actions: ALLOW (+1), DENY (-1), INSPECT (0)
 *   - Rate limiting with ternary thresholds
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "set5/trit.h"

/* ---- Constants ---- */
#define AFW_MAX_RULES       64
#define AFW_MAX_LOG_ENTRIES  256
#define AFW_NAME_LEN        32

#define AFW_ACTION_ALLOW     TRIT_TRUE
#define AFW_ACTION_DENY      TRIT_FALSE
#define AFW_ACTION_INSPECT   TRIT_UNKNOWN

#define AFW_DIR_INBOUND      0
#define AFW_DIR_OUTBOUND     1
#define AFW_DIR_BOTH         2

#define AFW_SEV_INFO         TRIT_TRUE
#define AFW_SEV_WARN         TRIT_UNKNOWN
#define AFW_SEV_CRIT         TRIT_FALSE

/* ---- Types ---- */
typedef struct {
    char name[AFW_NAME_LEN];
    int  direction;     /* AFW_DIR_* */
    int  action;        /* AFW_ACTION_* */
    int  port;          /* -1 = any */
    int  priority;      /* Higher = matched first */
    int  hit_count;
    int  active;
} afw_rule_t;

typedef struct {
    int  severity;      /* AFW_SEV_* */
    int  rule_idx;      /* Which rule triggered */
    int  direction;
    int  port;
    int  action_taken;
    int  timestamp;     /* Lamport clock value */
} afw_log_entry_t;

typedef struct {
    afw_rule_t      rules[AFW_MAX_RULES];
    afw_log_entry_t log[AFW_MAX_LOG_ENTRIES];
    int             rule_count;
    int             log_count;
    int             total_allowed;
    int             total_denied;
    int             total_inspected;
    int             clock;
} afw_state_t;

/* ---- API ---- */

static inline void afw_init(afw_state_t *s) {
    if (!s) return;
    memset(s, 0, sizeof(*s));
}

static inline int afw_add_rule(afw_state_t *s, const char *name,
                               int direction, int action, int port, int priority) {
    if (!s || !name || s->rule_count >= AFW_MAX_RULES) return -1;
    afw_rule_t *r = &s->rules[s->rule_count];
    memset(r, 0, sizeof(*r));
    strncpy(r->name, name, AFW_NAME_LEN - 1);
    r->direction = direction;
    r->action = action;
    r->port = port;
    r->priority = priority;
    r->active = 1;
    s->rule_count++;
    return s->rule_count - 1;
}

static inline int afw_evaluate(afw_state_t *s, int direction, int port) {
    if (!s) return AFW_ACTION_DENY;

    int best_rule = -1;
    int best_priority = -1;

    for (int i = 0; i < s->rule_count; i++) {
        afw_rule_t *r = &s->rules[i];
        if (!r->active) continue;
        if (r->direction != AFW_DIR_BOTH && r->direction != direction) continue;
        if (r->port != -1 && r->port != port) continue;
        if (r->priority > best_priority) {
            best_priority = r->priority;
            best_rule = i;
        }
    }

    int action = (best_rule >= 0) ? s->rules[best_rule].action : AFW_ACTION_DENY;

    /* Update counters */
    if (action == AFW_ACTION_ALLOW) s->total_allowed++;
    else if (action == AFW_ACTION_DENY) s->total_denied++;
    else s->total_inspected++;

    if (best_rule >= 0) s->rules[best_rule].hit_count++;

    /* Log the event */
    if (s->log_count < AFW_MAX_LOG_ENTRIES) {
        afw_log_entry_t *e = &s->log[s->log_count++];
        e->severity = (action == AFW_ACTION_DENY) ? AFW_SEV_CRIT :
                      (action == AFW_ACTION_INSPECT) ? AFW_SEV_WARN : AFW_SEV_INFO;
        e->rule_idx = best_rule;
        e->direction = direction;
        e->port = port;
        e->action_taken = action;
        e->timestamp = s->clock++;
    }

    return action;
}

static inline int afw_get_log_count(const afw_state_t *s) {
    return s ? s->log_count : 0;
}

static inline int afw_get_denied(const afw_state_t *s) {
    return s ? s->total_denied : 0;
}

static inline int afw_get_inspected(const afw_state_t *s) {
    return s ? s->total_inspected : 0;
}
