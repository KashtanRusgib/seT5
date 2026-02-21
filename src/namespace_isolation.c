/**
 * @file namespace_isolation.c
 * @brief T-017: Process Namespace Isolation via Ternary Capabilities
 *
 * Implements mount/PID/net namespace fencing using ternary capabilities:
 *   - TRIT_TRUE  = full access
 *   - TRIT_FALSE = denied
 *   - TRIT_UNKNOWN = sandboxed (restricted, logged)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "set5/trit.h"

/* ---- Constants ---- */
#define NS_MAX_PROCESSES    32
#define NS_MAX_NAMESPACES   16
#define NS_NAME_LEN         32

#define NS_TYPE_MOUNT       (1 << 0)
#define NS_TYPE_PID          (1 << 1)
#define NS_TYPE_NET          (1 << 2)
#define NS_TYPE_IPC          (1 << 3)
#define NS_TYPE_ALL          (NS_TYPE_MOUNT | NS_TYPE_PID | NS_TYPE_NET | NS_TYPE_IPC)
/* VULN-62: capability bit required to spawn processes in root namespace 0.
 * Without this, any caller with ns_id=0 gets unrestricted access. */
#define NS_CAP_ROOT_NS      (1 << 4)

/* Access results */
#define NS_ACCESS_GRANTED    TRIT_TRUE
#define NS_ACCESS_DENIED     TRIT_FALSE
#define NS_ACCESS_SANDBOXED  TRIT_UNKNOWN

/* ---- Types ---- */
typedef struct {
    char name[NS_NAME_LEN];
    int  type_mask;             /* Bitmask of NS_TYPE_* */
    int  access_policy;         /* Default: TRIT_TRUE/FALSE/UNKNOWN */
    int  process_count;
    int  active;
} ns_namespace_t;

typedef struct {
    int  pid;
    int  namespace_id;          /* Which namespace this process belongs to */
    int  capabilities;          /* Ternary capability bitmask */
    int  isolated;              /* TRIT_TRUE if fully isolated */
    int  violations;            /* Number of access violations */
} ns_process_t;

typedef struct {
    ns_namespace_t namespaces[NS_MAX_NAMESPACES];
    ns_process_t   processes[NS_MAX_PROCESSES];
    int            ns_count;
    int            proc_count;
    int            total_violations;
    int            total_sandboxed;
} ns_state_t;

/* ---- API ---- */

static inline void ns_init(ns_state_t *s) {
    if (!s) return;
    memset(s, 0, sizeof(*s));
    /* Create default root namespace */
    strncpy(s->namespaces[0].name, "root", NS_NAME_LEN - 1);
    s->namespaces[0].type_mask = NS_TYPE_ALL;
    s->namespaces[0].access_policy = NS_ACCESS_GRANTED;
    s->namespaces[0].active = 1;
    s->ns_count = 1;
}

static inline int ns_create(ns_state_t *s, const char *name, int type_mask, int policy) {
    if (!s || !name || s->ns_count >= NS_MAX_NAMESPACES) return -1;
    ns_namespace_t *ns = &s->namespaces[s->ns_count];
    memset(ns, 0, sizeof(*ns));
    strncpy(ns->name, name, NS_NAME_LEN - 1);
    ns->type_mask = type_mask;
    ns->access_policy = policy;
    ns->active = 1;
    s->ns_count++;
    return s->ns_count - 1;
}

static inline int ns_spawn_process(ns_state_t *s, int pid, int ns_id, int caps) {
    if (!s || s->proc_count >= NS_MAX_PROCESSES) return -1;
    if (ns_id < 0 || ns_id >= s->ns_count) return -1;    /* VULN-62 fix: spawning in the root namespace (ns_id==0) grants
     * unrestricted cross-namespace access to all resources. Require
     * NS_CAP_ROOT_NS capability to prevent privilege escalation via
     * accidental or malicious root-namespace spawn. */
    if (ns_id == 0 && !(caps & NS_CAP_ROOT_NS)) return -1;    ns_process_t *p = &s->processes[s->proc_count];
    p->pid = pid;
    p->namespace_id = ns_id;
    p->capabilities = caps;
    p->isolated = (ns_id > 0) ? TRIT_TRUE : TRIT_FALSE;
    p->violations = 0;
    s->namespaces[ns_id].process_count++;
    s->proc_count++;
    return s->proc_count - 1;
}

static inline int ns_check_access(ns_state_t *s, int proc_idx, int target_ns) {
    if (!s || proc_idx < 0 || proc_idx >= s->proc_count) return NS_ACCESS_DENIED;
    if (target_ns < 0 || target_ns >= s->ns_count) return NS_ACCESS_DENIED;

    ns_process_t *p = &s->processes[proc_idx];
    ns_namespace_t *ns = &s->namespaces[target_ns];

    /* Root namespace has full access — but audit the access for logging.
     * VULN-74 fix: root namespace still gets full access but we increment
     * a sandboxed counter so the audit trail captures root-ns operations
     * that cross namespace boundaries. This prevents silent privilege
     * escalation through root-ns. */
    if (p->namespace_id == 0) {
        if (target_ns != 0) s->total_sandboxed++;  /* cross-ns by root: audited */
        return NS_ACCESS_GRANTED;
    }

    /* Same namespace: use namespace policy */
    if (p->namespace_id == target_ns) return ns->access_policy;

    /* Cross-namespace: denied unless capabilities allow */
    if (p->capabilities & ns->type_mask) {
        s->total_sandboxed++;
        return NS_ACCESS_SANDBOXED;  /* Ternary Unknown = logged but permitted */
    }

    /* Violation */
    p->violations++;
    s->total_violations++;
    return NS_ACCESS_DENIED;
}

static inline int ns_get_violations(const ns_state_t *s) {
    return s ? s->total_violations : 0;
}

static inline int ns_is_isolated(const ns_state_t *s, int proc_idx) {
    if (!s || proc_idx < 0 || proc_idx >= s->proc_count) return TRIT_UNKNOWN;
    return s->processes[proc_idx].isolated;
}
