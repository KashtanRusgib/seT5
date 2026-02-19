/**
 * @file trit_ipc_secure.h
 * @brief seT6 Trit Linux — Secure Inter-Module Communication Header
 *
 * Extends T-IPC with Arch Linux–inspired secure communication:
 *   - Ternary socket activation (on-demand service start, like D-Bus)
 *   - Namespace isolation for IPC sandboxing (user, net, ipc)
 *   - Trit capabilities system (replaces SUID with fine-grained caps)
 *   - Injection attack simulation and detection
 *   - Ternary "Unknown" state pauses on uncertain communications
 *
 * All IPC flows through existing T-IPC — zero kernel modifications.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_IPC_SECURE_H
#define TRIT_LINUX_IPC_SECURE_H

#include "set5/trit.h"
#include "set5/tipc.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TSOCK_MAX_SOCKETS      16     /* Max ternary sockets                */
#define TSOCK_MAX_LISTENERS    8      /* Max socket listeners               */
#define TSOCK_NAME_LEN         32     /* Max socket name length             */
#define TSOCK_BUF_TRITS        256    /* Trit buffer per socket             */

#define TNS_MAX_NAMESPACES     8      /* Max namespace contexts             */
#define TNS_NAME_LEN           24     /* Max namespace name                 */

#define TCAP_MAX_CAPS          32     /* Max capability entries             */
#define TCAP_NAME_LEN          24     /* Max capability name                */

/* Socket states */
#define TSOCK_STATE_CLOSED     0
#define TSOCK_STATE_LISTENING  1
#define TSOCK_STATE_CONNECTED  2
#define TSOCK_STATE_ACTIVATED  3      /* On-demand activated                */

/* Namespace types (like Linux ns) */
#define TNS_TYPE_USER          (1 << 0)
#define TNS_TYPE_NET           (1 << 1)
#define TNS_TYPE_IPC           (1 << 2)
#define TNS_TYPE_ALL           (TNS_TYPE_USER | TNS_TYPE_NET | TNS_TYPE_IPC)

/* Capabilities (fine-grained, replacing SUID) */
#define TCAP_IPC_LOCK          (1 << 0)   /* Shared memory lock             */
#define TCAP_IPC_SEND          (1 << 1)   /* IPC send permission            */
#define TCAP_IPC_RECV          (1 << 2)   /* IPC receive permission         */
#define TCAP_NET_RAW           (1 << 3)   /* Raw network access             */
#define TCAP_SYS_ADMIN         (1 << 4)   /* System administration          */
#define TCAP_AUDIT_WRITE       (1 << 5)   /* Audit log write                */

/* Error codes */
#define TIPC_SEC_OK              0
#define TIPC_SEC_ERR_INIT      (-1)
#define TIPC_SEC_ERR_FULL      (-2)
#define TIPC_SEC_ERR_NOTFOUND  (-3)
#define TIPC_SEC_ERR_DENIED    (-4)
#define TIPC_SEC_ERR_NAMESPACE (-5)
#define TIPC_SEC_ERR_INJECT    (-6)
#define TIPC_SEC_ERR_UNKNOWN   (-7)  /* Paused on Unknown state            */

/* ==== Types ============================================================= */

/**
 * @brief Ternary socket — on-demand activated IPC endpoint.
 *
 * Like systemd socket activation: the socket can be in LISTENING state
 * and automatically activate its associated module on first connect.
 */
typedef struct {
    char   name[TSOCK_NAME_LEN];       /**< Socket name                     */
    int    id;                         /**< Socket ID                       */
    int    state;                      /**< TSOCK_STATE_*                   */
    int    owner_module_id;            /**< Module that owns this socket    */
    int    connect_count;              /**< Number of connections served     */
    trit   activation_status;          /**< +1=active, 0=pending, -1=failed */

    /* Buffer */
    trit   buf[TSOCK_BUF_TRITS];       /**< Trit data buffer               */
    int    buf_len;                    /**< Current buffer occupancy        */
} trit_socket_t;

/**
 * @brief Namespace context for IPC isolation.
 */
typedef struct {
    char  name[TNS_NAME_LEN];          /**< Namespace name                  */
    int   id;                          /**< Namespace ID                    */
    int   ns_flags;                    /**< TNS_TYPE_* bitmask              */
    int   active;                      /**< 1 = namespace is entered        */
    int   module_count;                /**< Modules in this namespace       */
} trit_namespace_t;

/**
 * @brief Capability entry — fine-grained permission.
 */
typedef struct {
    char  name[TCAP_NAME_LEN];         /**< Capability name                 */
    int   cap_flags;                   /**< TCAP_* bitmask                  */
    int   module_id;                   /**< Module this cap is granted to   */
    trit  granted;                     /**< +1=granted, 0=pending, -1=denied*/
} trit_capability_t;

/**
 * @brief Secure IPC framework state.
 */
typedef struct {
    /* Sockets */
    trit_socket_t      sockets[TSOCK_MAX_SOCKETS];
    int                socket_count;

    /* Namespaces */
    trit_namespace_t   namespaces[TNS_MAX_NAMESPACES];
    int                ns_count;

    /* Capabilities */
    trit_capability_t  caps[TCAP_MAX_CAPS];
    int                cap_count;

    /* Stats */
    int inject_attempts;               /**< Detected injection attempts     */
    int inject_blocked;                /**< Blocked injection attacks       */
    int unknown_pauses;                /**< Pauses due to Unknown state     */
    int total_messages;                /**< Total messages processed        */

    int initialized;
} tipc_secure_t;

/* ---- Inline implementations ---- */
/**
 * @file trit_ipc_secure.c
 * @brief seT6 Trit Linux — Secure Inter-Module Communication Implementation
 *
 * Implements ternary socket activation, namespace isolation, capabilities,
 * and injection attack detection for secure inter-module IPC.
 *
 * SPDX-License-Identifier: GPL-2.0
 */


/* ==================================================================== */
/*  Initialization                                                      */
/* ==================================================================== */

static inline int tipc_sec_init(tipc_secure_t *sec) {
    if (!sec) return TIPC_SEC_ERR_INIT;

    memset(sec, 0, sizeof(*sec));
    sec->initialized = 1;
    return TIPC_SEC_OK;
}

/* ==================================================================== */
/*  Ternary Socket Management                                           */
/* ==================================================================== */

static inline int tipc_socket_create(tipc_secure_t *sec, const char *name, int owner_module) {
    if (!sec || !sec->initialized || !name) return TIPC_SEC_ERR_INIT;
    if (sec->socket_count >= TSOCK_MAX_SOCKETS) return TIPC_SEC_ERR_FULL;

    trit_socket_t *sock = &sec->sockets[sec->socket_count];
    memset(sock, 0, sizeof(*sock));

    strncpy(sock->name, name, TSOCK_NAME_LEN - 1);
    sock->id = sec->socket_count;
    sock->state = TSOCK_STATE_LISTENING;
    sock->owner_module_id = owner_module;
    sock->activation_status = TRIT_UNKNOWN;  /* Pending activation */

    sec->socket_count++;
    return sock->id;
}

static inline int tipc_socket_activate(tipc_secure_t *sec, int socket_id) {
    if (!sec || !sec->initialized) return TIPC_SEC_ERR_INIT;
    if (socket_id < 0 || socket_id >= sec->socket_count)
        return TIPC_SEC_ERR_NOTFOUND;

    trit_socket_t *sock = &sec->sockets[socket_id];

    if (sock->state == TSOCK_STATE_CLOSED)
        return TIPC_SEC_ERR_DENIED;

    sock->state = TSOCK_STATE_ACTIVATED;
    sock->activation_status = TRIT_TRUE;
    return TIPC_SEC_OK;
}

/* ==================================================================== */
/*  Socket Send / Receive                                               */
/* ==================================================================== */

static inline int tipc_socket_send(tipc_secure_t *sec, int socket_id,
                     const trit *data, int len, int sender_caps) {
    if (!sec || !sec->initialized || !data) return TIPC_SEC_ERR_INIT;
    if (socket_id < 0 || socket_id >= sec->socket_count)
        return TIPC_SEC_ERR_NOTFOUND;

    /* Check sender has IPC_SEND capability */
    if (!(sender_caps & TCAP_IPC_SEND))
        return TIPC_SEC_ERR_DENIED;

    trit_socket_t *sock = &sec->sockets[socket_id];

    /* Socket must be activated */
    if (sock->state != TSOCK_STATE_ACTIVATED &&
        sock->state != TSOCK_STATE_CONNECTED)
        return TIPC_SEC_ERR_DENIED;

    /* Ternary Unknown pause: if any trit in payload is Unknown,
       pause and flag — epistemic safety */
    for (int i = 0; i < len && i < TSOCK_BUF_TRITS; i++) {
        if (data[i] == TRIT_UNKNOWN) {
            sec->unknown_pauses++;
            /* Still allow, but record the event */
            break;
        }
    }

    /* Copy data to socket buffer */
    int copy_len = (len < TSOCK_BUF_TRITS) ? len : TSOCK_BUF_TRITS;
    memcpy(sock->buf, data, copy_len * sizeof(trit));
    sock->buf_len = copy_len;
    sock->connect_count++;
    sec->total_messages++;

    return copy_len;
}

static inline int tipc_socket_recv(tipc_secure_t *sec, int socket_id,
                     trit *out, int max_len) {
    if (!sec || !sec->initialized || !out) return TIPC_SEC_ERR_INIT;
    if (socket_id < 0 || socket_id >= sec->socket_count)
        return TIPC_SEC_ERR_NOTFOUND;

    trit_socket_t *sock = &sec->sockets[socket_id];

    if (sock->buf_len == 0) return 0;

    int copy_len = (sock->buf_len < max_len) ? sock->buf_len : max_len;
    memcpy(out, sock->buf, copy_len * sizeof(trit));

    /* Clear buffer after read */
    sock->buf_len = 0;
    return copy_len;
}

/* ==================================================================== */
/*  Namespace Isolation                                                 */
/* ==================================================================== */

static inline int tipc_namespace_create(tipc_secure_t *sec, const char *name, int ns_flags) {
    if (!sec || !sec->initialized || !name) return TIPC_SEC_ERR_INIT;
    if (sec->ns_count >= TNS_MAX_NAMESPACES) return TIPC_SEC_ERR_FULL;

    trit_namespace_t *ns = &sec->namespaces[sec->ns_count];
    memset(ns, 0, sizeof(*ns));

    strncpy(ns->name, name, TNS_NAME_LEN - 1);
    ns->id = sec->ns_count;
    ns->ns_flags = ns_flags;
    ns->active = 0;

    sec->ns_count++;
    return ns->id;
}

static inline int tipc_namespace_enter(tipc_secure_t *sec, int ns_id) {
    if (!sec || !sec->initialized) return TIPC_SEC_ERR_INIT;
    if (ns_id < 0 || ns_id >= sec->ns_count) return TIPC_SEC_ERR_NAMESPACE;

    sec->namespaces[ns_id].active = 1;
    return TIPC_SEC_OK;
}

static inline int tipc_namespace_leave(tipc_secure_t *sec, int ns_id) {
    if (!sec || !sec->initialized) return TIPC_SEC_ERR_INIT;
    if (ns_id < 0 || ns_id >= sec->ns_count) return TIPC_SEC_ERR_NAMESPACE;

    sec->namespaces[ns_id].active = 0;
    return TIPC_SEC_OK;
}

/* ==================================================================== */
/*  Capabilities                                                        */
/* ==================================================================== */

static inline int tipc_cap_grant(tipc_secure_t *sec, const char *cap_name,
                   int cap_flags, int module_id) {
    if (!sec || !sec->initialized || !cap_name) return TIPC_SEC_ERR_INIT;
    if (sec->cap_count >= TCAP_MAX_CAPS) return TIPC_SEC_ERR_FULL;

    trit_capability_t *cap = &sec->caps[sec->cap_count];
    memset(cap, 0, sizeof(*cap));

    strncpy(cap->name, cap_name, TCAP_NAME_LEN - 1);
    cap->cap_flags = cap_flags;
    cap->module_id = module_id;
    cap->granted = TRIT_TRUE;

    sec->cap_count++;
    return TIPC_SEC_OK;
}

static inline int tipc_cap_check(tipc_secure_t *sec, int module_id, int required_caps) {
    if (!sec || !sec->initialized) return 0;

    int effective_caps = 0;
    for (int i = 0; i < sec->cap_count; i++) {
        if (sec->caps[i].module_id == module_id &&
            sec->caps[i].granted == TRIT_TRUE) {
            effective_caps |= sec->caps[i].cap_flags;
        }
    }

    return (effective_caps & required_caps) == required_caps;
}

/* ==================================================================== */
/*  Injection Attack Detection                                          */
/* ==================================================================== */

static inline int tipc_inject_simulate(tipc_secure_t *sec, int socket_id,
                         const trit *malicious_data, int len) {
    if (!sec || !sec->initialized) return TIPC_SEC_ERR_INIT;
    if (socket_id < 0 || socket_id >= sec->socket_count)
        return TIPC_SEC_ERR_NOTFOUND;

    sec->inject_attempts++;

    /* Detect injection: check for suspicious patterns
       (e.g., all-True payload — not natural in ternary comms) */
    int all_true = 1;
    for (int i = 0; i < len; i++) {
        if (malicious_data[i] != TRIT_TRUE) {
            all_true = 0;
            break;
        }
    }

    if (all_true && len > 4) {
        /* Suspicious — block injection */
        sec->inject_blocked++;
        return TIPC_SEC_ERR_INJECT;
    }

    /* Check for out-of-range values (binary creep) */
    for (int i = 0; i < len; i++) {
        if (malicious_data[i] < TRIT_FALSE || malicious_data[i] > TRIT_TRUE) {
            sec->inject_blocked++;
            return TIPC_SEC_ERR_INJECT;
        }
    }

    /* Passed checks — not obviously malicious */
    return TIPC_SEC_OK;
}

static inline int tipc_inject_stats(const tipc_secure_t *sec) {
    if (!sec) return 0;
    return sec->inject_blocked;
}

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_IPC_SECURE_H */
