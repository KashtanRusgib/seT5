/**
 * @file ipc.h
 * @brief seT6 Inter-Process Communication — Endpoints & Notifications
 *
 * seL4-style IPC with ternary extensions:
 *   - Synchronous message passing via endpoints (blocking send/recv)
 *   - Asynchronous notifications (non-blocking signal/wait)
 *   - Capability-guarded: all IPC requires a valid capability
 *   - Ternary message payloads: each word is a trit (can carry Unknown)
 *   - Badge discrimination: sender identity encoded in cap badge
 *
 * IPC states (ternary):
 *   - Endpoint idle:    valid = Unknown (no sender/receiver waiting)
 *   - Sender waiting:   valid = True    (message buffered)
 *   - Receiver waiting: valid = False   (consumer blocked)
 *
 * @see ARCHITECTURE.md §6 — IPC Model
 * @see set6.h for syscall numbers (SYS_CAP_SEND, SYS_CAP_RECV)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_IPC_H
#define SET6_IPC_H

#include "set6/trit.h"
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Configuration ---------------------------------------------------- */

/** Maximum words in an IPC message */
#define IPC_MSG_MAX_WORDS    16

/** Maximum endpoints in the system */
#define IPC_MAX_ENDPOINTS    32

/** Maximum notifications in the system */
#define IPC_MAX_NOTIFICATIONS 16

/* ---- Message ---------------------------------------------------------- */

/** IPC message: fixed-size array of trit words + metadata */
typedef struct {
    trit  words[IPC_MSG_MAX_WORDS];  /**< Trit payload (Unknown = unused) */
    int   length;                     /**< Number of valid words */
    int   sender_badge;               /**< Badge from sender's capability */
    int   sender_tid;                 /**< Sender thread ID */
} ipc_msg_t;

/* ---- Endpoint --------------------------------------------------------- */

typedef enum {
    EP_IDLE,              /**< No threads waiting */
    EP_SEND_BLOCKED,      /**< Sender waiting for receiver */
    EP_RECV_BLOCKED       /**< Receiver waiting for sender */
} ep_state_t;

/** IPC endpoint: synchronous rendezvous point */
typedef struct {
    trit        valid;              /**< T=active, U=idle, F=destroyed */
    ep_state_t  state;              /**< Current endpoint state */
    ipc_msg_t   buffered_msg;       /**< Message waiting for delivery */
    int         blocked_tid;        /**< Thread ID waiting on this endpoint */
    int         object_id;          /**< Kernel object identifier */
} ipc_endpoint_t;

/* ---- Notification ----------------------------------------------------- */

/** Asynchronous notification: bitmap-style signal word */
typedef struct {
    trit  valid;                    /**< T=active, F=destroyed */
    trit  signal_word;              /**< Trit signal: T=signaled, U=none */
    int   waiting_tid;              /**< Thread waiting for signal (-1=none) */
    int   object_id;                /**< Kernel object identifier */
} ipc_notification_t;

/* ---- IPC Manager State ------------------------------------------------ */

typedef struct {
    ipc_endpoint_t     endpoints[IPC_MAX_ENDPOINTS];
    int                ep_count;
    ipc_notification_t notifications[IPC_MAX_NOTIFICATIONS];
    int                notif_count;
} ipc_state_t;

/* ---- API -------------------------------------------------------------- */

/**
 * @brief Initialise the IPC subsystem.
 * @param ipc  Pointer to IPC state.
 */
void ipc_init(ipc_state_t *ipc);

/**
 * @brief Create a new endpoint.
 * @param ipc  IPC state.
 * @return Endpoint index (>= 0) on success, -1 on failure.
 */
int ipc_endpoint_create(ipc_state_t *ipc);

/**
 * @brief Destroy an endpoint.
 * @param ipc    IPC state.
 * @param ep_idx Endpoint index.
 * @return 0 on success, -1 on failure.
 */
int ipc_endpoint_destroy(ipc_state_t *ipc, int ep_idx);

/**
 * @brief Send a message on an endpoint (synchronous).
 *
 * If a receiver is blocked on this endpoint, the message is delivered
 * immediately and the receiver is unblocked.  Otherwise, the message
 * is buffered and the sender blocks.
 *
 * @param ipc       IPC state.
 * @param ep_idx    Endpoint to send on.
 * @param msg       Message to send.
 * @param sender_tid Sending thread's ID.
 * @return 0 on immediate delivery, 1 if sender blocks, -1 on error.
 */
int ipc_send(ipc_state_t *ipc, int ep_idx, const ipc_msg_t *msg,
             int sender_tid);

/**
 * @brief Receive a message from an endpoint (synchronous).
 *
 * If a sender is blocked with a buffered message, dequeues it immediately.
 * Otherwise, the receiver blocks.
 *
 * @param ipc       IPC state.
 * @param ep_idx    Endpoint to receive on.
 * @param[out] msg  Buffer to receive message into.
 * @param recv_tid  Receiving thread's ID.
 * @return 0 on immediate receive, 1 if receiver blocks, -1 on error.
 */
int ipc_recv(ipc_state_t *ipc, int ep_idx, ipc_msg_t *msg, int recv_tid);

/**
 * @brief Create a notification object.
 * @param ipc  IPC state.
 * @return Notification index (>= 0) on success, -1 on failure.
 */
int ipc_notification_create(ipc_state_t *ipc);

/**
 * @brief Signal a notification (asynchronous, non-blocking).
 * @param ipc       IPC state.
 * @param notif_idx Notification index.
 * @return 0 on success, -1 on failure.
 */
int ipc_signal(ipc_state_t *ipc, int notif_idx);

/**
 * @brief Wait on a notification (blocks until signal arrives).
 * @param ipc       IPC state.
 * @param notif_idx Notification index.
 * @param wait_tid  Waiting thread's ID.
 * @return 0 if signal already pending, 1 if must block, -1 on error.
 */
int ipc_wait(ipc_state_t *ipc, int notif_idx, int wait_tid);

/**
 * @brief Build an IPC message from trit words.
 * @param msg       Message buffer to fill.
 * @param words     Array of trit values.
 * @param length    Number of words (≤ IPC_MSG_MAX_WORDS).
 * @param badge     Sender badge.
 * @param sender    Sender thread ID.
 */
void ipc_msg_build(ipc_msg_t *msg, const trit *words, int length,
                   int badge, int sender);

#ifdef __cplusplus
}
#endif

#endif /* SET6_IPC_H */
