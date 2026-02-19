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

/* ==== API =============================================================== */

/** Initialize the secure IPC framework. */
int tipc_sec_init(tipc_secure_t *sec);

/** Create a ternary socket with on-demand activation. */
int tipc_socket_create(tipc_secure_t *sec, const char *name, int owner_module);

/** Activate a socket (transition from LISTENING to ACTIVATED). */
int tipc_socket_activate(tipc_secure_t *sec, int socket_id);

/** Send trits through a socket (checks capabilities). */
int tipc_socket_send(tipc_secure_t *sec, int socket_id,
                     const trit *data, int len, int sender_caps);

/** Receive trits from a socket (checks namespace). */
int tipc_socket_recv(tipc_secure_t *sec, int socket_id,
                     trit *out, int max_len);

/** Create a namespace for IPC isolation. */
int tipc_namespace_create(tipc_secure_t *sec, const char *name, int ns_flags);

/** Enter a namespace (activate isolation). */
int tipc_namespace_enter(tipc_secure_t *sec, int ns_id);

/** Leave a namespace. */
int tipc_namespace_leave(tipc_secure_t *sec, int ns_id);

/** Grant a capability to a module. */
int tipc_cap_grant(tipc_secure_t *sec, const char *cap_name,
                   int cap_flags, int module_id);

/** Check if a module has a specific capability. */
int tipc_cap_check(tipc_secure_t *sec, int module_id, int required_caps);

/** Simulate an injection attack — should be blocked. */
int tipc_inject_simulate(tipc_secure_t *sec, int socket_id,
                         const trit *malicious_data, int len);

/** Get injection stats. */
int tipc_inject_stats(const tipc_secure_t *sec);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_IPC_SECURE_H */
