/**
 * @file ipc.c
 * @brief seT5 IPC — Synchronous Endpoints & Async Notifications
 *
 * seL4-style IPC with ternary extensions:
 *   - Synchronous: blocking send/recv with rendezvous
 *   - Asynchronous: non-blocking signal/wait notifications
 *   - All payloads are trit words (Unknown propagates correctly)
 *   - Badge-based sender identification
 *
 * Ternary advantage: message slots initialised to Unknown, so
 * a receiver can distinguish "sender wrote zero" from "slot unused".
 *
 * @see include/set5/ipc.h for API documentation
 * @see ARCHITECTURE.md §6 — IPC Model
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/ipc.h"
#include <string.h>

/* ==== Initialisation =================================================== */

void ipc_init(ipc_state_t *ipc) {
    if (!ipc) return;

    ipc->ep_count    = 0;
    ipc->notif_count = 0;

    for (int i = 0; i < IPC_MAX_ENDPOINTS; i++) {
        ipc_endpoint_t *ep = &ipc->endpoints[i];
        ep->valid       = TRIT_FALSE;
        ep->state       = EP_IDLE;
        ep->blocked_tid = -1;
        ep->object_id   = -1;
        /* Clear buffered message */
        memset(&ep->buffered_msg, 0, sizeof(ipc_msg_t));
        for (int w = 0; w < IPC_MSG_MAX_WORDS; w++)
            ep->buffered_msg.words[w] = TRIT_UNKNOWN;
    }

    for (int i = 0; i < IPC_MAX_NOTIFICATIONS; i++) {
        ipc_notification_t *n = &ipc->notifications[i];
        n->valid       = TRIT_FALSE;
        n->signal_word = TRIT_UNKNOWN;  /* no signal pending */
        n->waiting_tid = -1;
        n->object_id   = -1;
    }
}

/* ==== Endpoint Management ============================================== */

int ipc_endpoint_create(ipc_state_t *ipc) {
    if (!ipc || ipc->ep_count >= IPC_MAX_ENDPOINTS) return -1;

    int idx = ipc->ep_count++;
    ipc_endpoint_t *ep = &ipc->endpoints[idx];
    ep->valid       = TRIT_TRUE;  /* active */
    ep->state       = EP_IDLE;
    ep->blocked_tid = -1;
    ep->object_id   = idx;

    /* Init buffered message to Unknown */
    ep->buffered_msg.length       = 0;
    ep->buffered_msg.sender_badge = 0;
    ep->buffered_msg.sender_tid   = -1;
    for (int w = 0; w < IPC_MSG_MAX_WORDS; w++)
        ep->buffered_msg.words[w] = TRIT_UNKNOWN;

    return idx;
}

int ipc_endpoint_destroy(ipc_state_t *ipc, int ep_idx) {
    if (!ipc) return -1;
    if (ep_idx < 0 || ep_idx >= ipc->ep_count) return -1;

    ipc_endpoint_t *ep = &ipc->endpoints[ep_idx];
    if (ep->valid != TRIT_TRUE) return -1;  /* already destroyed */

    /* VULN-16 fix: record blocked thread before clearing,
     * so scheduler can unblock it after destroy */
    int was_blocked_tid = ep->blocked_tid;

    ep->valid       = TRIT_FALSE;  /* mark destroyed */
    ep->state       = EP_IDLE;
    ep->blocked_tid = -1;
    /* VULN-53 note: Return convention for endpoint_destroy:
     *   0           = success, no thread was blocked (or TID-0 was blocked)
     *   positive N  = success, thread N needs unblocking
     *   -1          = error (invalid ep_idx, already destroyed, etc.)
     * TID-0 is the kernel/idle thread and should never block on an IPC
     * endpoint, so the 0-vs-TID-0 ambiguity is harmless in practice.
     * If TID-0 blocking becomes possible, change to return tid+1. */
    return (was_blocked_tid >= 0) ? was_blocked_tid : 0;
}

/* ==== Synchronous Send/Recv ============================================ */

int ipc_send(ipc_state_t *ipc, int ep_idx, const ipc_msg_t *msg,
             int sender_tid) {
    if (!ipc || !msg) return -1;
    if (ep_idx < 0 || ep_idx >= ipc->ep_count) return -1;

    ipc_endpoint_t *ep = &ipc->endpoints[ep_idx];
    if (ep->valid != TRIT_TRUE) return -1;

    /* VULN-15 fix: snapshot state once for atomic check+mutate */
    int ep_state = ep->state;

    if (ep_state == EP_RECV_BLOCKED) {
        /* Receiver is waiting — deliver immediately (rendezvous) */
        ep->buffered_msg = *msg;
        ep->buffered_msg.sender_tid = sender_tid;
        ep->state = EP_IDLE;
        /* Receiver should be unblocked by scheduler (signaled here) */
        ep->blocked_tid = -1;
        return 0;  /* immediate delivery */
    }

    /* VULN-57 fix: if a sender is already blocked, reject the second send.
     * Allowing overwrite would orphan the first sender (perma-blocked) and
     * allow message injection into the channel. Return -1 (EBUSY). */
    if (ep_state == EP_SEND_BLOCKED) {
        return -1;  /* endpoint busy — first sender still pending */
    }

    /* No receiver — buffer the message and block sender */
    ep->buffered_msg = *msg;
    ep->buffered_msg.sender_tid = sender_tid;
    ep->state       = EP_SEND_BLOCKED;
    ep->blocked_tid = sender_tid;
    return 1;  /* sender blocks */
}

int ipc_recv(ipc_state_t *ipc, int ep_idx, ipc_msg_t *msg, int recv_tid) {
    if (!ipc || !msg) return -1;
    if (ep_idx < 0 || ep_idx >= ipc->ep_count) return -1;

    ipc_endpoint_t *ep = &ipc->endpoints[ep_idx];
    if (ep->valid != TRIT_TRUE) return -1;

    /* VULN-15 fix: snapshot state once for atomic check+mutate */
    int ep_state = ep->state;

    if (ep_state == EP_SEND_BLOCKED) {
        /* Sender is waiting — dequeue immediately */
        *msg = ep->buffered_msg;
        ep->state = EP_IDLE;
        ep->blocked_tid = -1;
        /* Sender should be unblocked by scheduler */
        return 0;  /* immediate receive */
    }

    /* No sender — block receiver */
    ep->state       = EP_RECV_BLOCKED;
    ep->blocked_tid = recv_tid;
    return 1;  /* receiver blocks */
}

/* ==== Notification Management ========================================== */

int ipc_notification_create(ipc_state_t *ipc) {
    if (!ipc || ipc->notif_count >= IPC_MAX_NOTIFICATIONS) return -1;

    int idx = ipc->notif_count++;
    ipc_notification_t *n = &ipc->notifications[idx];
    n->valid       = TRIT_TRUE;
    n->signal_word = TRIT_UNKNOWN;  /* no signal */
    n->waiting_tid = -1;
    n->object_id   = idx;
    return idx;
}

int ipc_signal(ipc_state_t *ipc, int notif_idx) {
    if (!ipc) return -1;
    if (notif_idx < 0 || notif_idx >= ipc->notif_count) return -1;

    ipc_notification_t *n = &ipc->notifications[notif_idx];
    if (n->valid != TRIT_TRUE) return -1;

    n->signal_word = TRIT_TRUE;  /* signal! */

    /* If a thread is waiting, it should be unblocked by scheduler */
    if (n->waiting_tid >= 0) {
        /* Clear waiting state — scheduler will pick it up */
        n->waiting_tid = -1;
    }
    return 0;
}

int ipc_wait(ipc_state_t *ipc, int notif_idx, int wait_tid) {
    if (!ipc) return -1;
    if (notif_idx < 0 || notif_idx >= ipc->notif_count) return -1;

    ipc_notification_t *n = &ipc->notifications[notif_idx];
    if (n->valid != TRIT_TRUE) return -1;

    if (n->signal_word == TRIT_TRUE) {
        /* Signal already pending — consume immediately */
        n->signal_word = TRIT_UNKNOWN;  /* clear */
        return 0;
    }

    /* No signal — block */
    n->waiting_tid = wait_tid;
    return 1;  /* must block */
}

/* ==== Message Builder ================================================== */

void ipc_msg_build(ipc_msg_t *msg, const trit *words, int length,
                   int badge, int sender) {
    if (!msg) return;

    /* Init all slots to Unknown first */
    for (int w = 0; w < IPC_MSG_MAX_WORDS; w++)
        msg->words[w] = TRIT_UNKNOWN;

    /* Copy provided words */
    if (length > IPC_MSG_MAX_WORDS)
        length = IPC_MSG_MAX_WORDS;
    if (words && length > 0) {
        for (int i = 0; i < length; i++)
            msg->words[i] = words[i];
    }

    msg->length       = length;
    msg->sender_badge = badge;
    msg->sender_tid   = sender;
}
