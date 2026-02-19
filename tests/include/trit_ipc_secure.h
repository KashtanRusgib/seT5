/**
 * @file trit_ipc_secure.h
 * @brief seT6 — Secure IPC framework (inline implementation)
 * SPDX-License-Identifier: GPL-2.0
 */
#ifndef TRIT_IPC_SECURE_H
#define TRIT_IPC_SECURE_H

#include <string.h>
#include <stdint.h>
#include "set5/trit.h"

#define TIPC_SEC_OK            0
#define TIPC_SEC_ERR_INIT     (-1)
#define TIPC_SEC_ERR_NOTFOUND (-2)
#define TIPC_SEC_ERR_DENIED   (-3)
#define TIPC_SEC_ERR_NAMESPACE (-4)
#define TIPC_SEC_ERR_INJECT   (-5)

#define TCAP_IPC_SEND  0x01
#define TCAP_IPC_LOCK  0x02
#define TCAP_SYS_ADMIN 0x04
#define TCAP_NET_RAW   0x08

#define TNS_TYPE_USER  0x01
#define TNS_TYPE_IPC   0x02
#define TNS_TYPE_NET   0x04

#define TSOCK_STATE_LISTENING  0
#define TSOCK_STATE_ACTIVATED  1

#define TIPC_SEC_MAX_SOCKETS 16
#define TIPC_SEC_MAX_NS      8
#define TIPC_SEC_MAX_CAPS    8
#define TIPC_SEC_BUF_LEN     256

typedef struct {
    char  name[32];
    int   ns_id;
    int   state;
    trit  activation_status;
    trit  buf[TIPC_SEC_BUF_LEN];
    int   buf_len;
} tipc_sec_sock_t;

typedef struct {
    char name[32];
    int  type;
    int  active;
} tipc_namespace_t;

typedef struct {
    char    label[32];
    int     caps;
    int     module_id;
} tipc_cap_entry_t;

typedef struct {
    tipc_sec_sock_t  sockets[TIPC_SEC_MAX_SOCKETS];
    int              socket_count;
    tipc_namespace_t namespaces[TIPC_SEC_MAX_NS];
    int              ns_count;
    tipc_cap_entry_t cap_entries[TIPC_SEC_MAX_CAPS];
    int              cap_count;
    int              unknown_pauses;
    int              total_messages;
    int              inject_attempts;
    int              inject_blocked;
} tipc_secure_t;

static inline int tipc_sec_init(tipc_secure_t *s) {
    if (!s) return TIPC_SEC_ERR_INIT;
    memset(s, 0, sizeof(*s));
    return TIPC_SEC_OK;
}

static inline int tipc_socket_create(tipc_secure_t *s, const char *name, int ns_id) {
    if (!s || s->socket_count >= TIPC_SEC_MAX_SOCKETS) return -1;
    int id = s->socket_count++;
    memset(&s->sockets[id], 0, sizeof(tipc_sec_sock_t));
    strncpy(s->sockets[id].name, name, 31);
    s->sockets[id].ns_id = ns_id;
    s->sockets[id].state = TSOCK_STATE_LISTENING;
    s->sockets[id].activation_status = TRIT_UNKNOWN;
    return id;
}

static inline int tipc_socket_activate(tipc_secure_t *s, int sid) {
    if (!s || sid < 0 || sid >= s->socket_count) return TIPC_SEC_ERR_NOTFOUND;
    s->sockets[sid].state = TSOCK_STATE_ACTIVATED;
    s->sockets[sid].activation_status = TRIT_TRUE;
    return TIPC_SEC_OK;
}

static inline int tipc_socket_send(tipc_secure_t *s, int sid, const trit *data, int len, int caps) {
    if (!s || sid < 0 || sid >= s->socket_count) return TIPC_SEC_ERR_NOTFOUND;
    if (!(caps & TCAP_IPC_SEND)) return TIPC_SEC_ERR_DENIED;
    if (len > TIPC_SEC_BUF_LEN) len = TIPC_SEC_BUF_LEN;
    memcpy(s->sockets[sid].buf, data, len * sizeof(trit));
    s->sockets[sid].buf_len = len;
    for (int i = 0; i < len; i++)
        if (data[i] == TRIT_UNKNOWN) { s->unknown_pauses++; break; }
    s->total_messages++;
    return len;
}

static inline int tipc_socket_recv(tipc_secure_t *s, int sid, trit *out, int maxlen) {
    if (!s || sid < 0 || sid >= s->socket_count) return 0;
    int n = s->sockets[sid].buf_len;
    if (n == 0) return 0;
    if (n > maxlen) n = maxlen;
    memcpy(out, s->sockets[sid].buf, n * sizeof(trit));
    s->sockets[sid].buf_len = 0;
    return n;
}

static inline int tipc_namespace_create(tipc_secure_t *s, const char *name, int type) {
    if (!s || s->ns_count >= TIPC_SEC_MAX_NS) return -1;
    int id = s->ns_count++;
    memset(&s->namespaces[id], 0, sizeof(tipc_namespace_t));
    strncpy(s->namespaces[id].name, name, 31);
    s->namespaces[id].type = type;
    return id;
}

static inline int tipc_namespace_enter(tipc_secure_t *s, int nsid) {
    if (!s || nsid < 0 || nsid >= s->ns_count) return TIPC_SEC_ERR_NAMESPACE;
    s->namespaces[nsid].active = 1;
    return TIPC_SEC_OK;
}

static inline int tipc_namespace_leave(tipc_secure_t *s, int nsid) {
    if (!s || nsid < 0 || nsid >= s->ns_count) return TIPC_SEC_ERR_NAMESPACE;
    s->namespaces[nsid].active = 0;
    return TIPC_SEC_OK;
}

static inline int tipc_cap_grant(tipc_secure_t *s, const char *label, int caps, int module_id) {
    if (!s || s->cap_count >= TIPC_SEC_MAX_CAPS) return -1;
    /* Merge if module already has an entry */
    for (int i = 0; i < s->cap_count; i++) {
        if (s->cap_entries[i].module_id == module_id) {
            s->cap_entries[i].caps |= caps;
            return TIPC_SEC_OK;
        }
    }
    int c = s->cap_count++;
    strncpy(s->cap_entries[c].label, label, 31);
    s->cap_entries[c].caps = caps;
    s->cap_entries[c].module_id = module_id;
    return TIPC_SEC_OK;
}

static inline int tipc_cap_check(tipc_secure_t *s, int module_id, int cap) {
    for (int i = 0; i < s->cap_count; i++)
        if (s->cap_entries[i].module_id == module_id && (s->cap_entries[i].caps & cap))
            return 1;
    return 0;
}

static inline int tipc_inject_simulate(tipc_secure_t *s, int sid, const trit *data, int len) {
    s->inject_attempts++;
    /* Detect suspicious all-same pattern */
    int all_same = 1;
    for (int i = 1; i < len; i++)
        if (data[i] != data[0]) { all_same = 0; break; }
    if (all_same && len >= 4) {
        s->inject_blocked++;
        return TIPC_SEC_ERR_INJECT;
    }
    return TIPC_SEC_OK;
}

static inline int tipc_inject_stats(tipc_secure_t *s) {
    return s->inject_blocked;
}

#endif /* TRIT_IPC_SECURE_H */
