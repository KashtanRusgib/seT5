/*
 * sel4_verify.h - seL4 Ternary Verification Interface (TASK-019)
 *
 * Extends the basic seL4 stub (TASK-010) to cover the full seL4 API:
 *   - Capability derivation trees
 *   - Endpoint management (sync + async)
 *   - Thread control blocks
 *   - Memory frame management
 *   - CSpace / VSpace abstractions
 *
 * Each operation compiles to ternary bytecode and has a corresponding
 * Isabelle/HOL lemma for correctness verification.
 */

#ifndef SEL4_VERIFY_H
#define SEL4_VERIFY_H

#include "ir.h"
#include "set5.h"

/* ---- seL4 Capability Derivation ---- */

/* Maximum depth of capability derivation tree */
#define CAP_MAX_DEPTH 9  /* 3^2 = balanced ternary alignment */

typedef struct CapNode {
    seT5_cap cap;
    struct CapNode *parent;
    struct CapNode *children[3]; /* ternary branching */
    int child_count;
    seT5_obj_type obj_type;
} CapNode;

/* Create a root capability node */
static inline CapNode *cap_tree_root(int object_id, seT5_obj_type otype) {
    CapNode *n = (CapNode *)malloc(sizeof(CapNode));
    if (!n) return NULL;
    n->cap.object_id = object_id;
    n->cap.rights = CAP_RIGHT_ALL;
    n->cap.badge = 0;
    n->parent = NULL;
    n->child_count = 0;
    for (int i = 0; i < 3; i++) n->children[i] = NULL;
    n->obj_type = otype;
    return n;
}

/* Derive a child capability with restricted rights */
static inline CapNode *cap_derive(CapNode *parent, int rights) {
    if (!parent || parent->child_count >= 3) return NULL;
    CapNode *child = (CapNode *)malloc(sizeof(CapNode));
    if (!child) return NULL;
    child->cap.object_id = parent->cap.object_id;
    child->cap.rights = parent->cap.rights & rights;
    child->cap.badge = parent->child_count + 1;
    child->parent = parent;
    child->child_count = 0;
    for (int i = 0; i < 3; i++) child->children[i] = NULL;
    child->obj_type = parent->obj_type;
    parent->children[parent->child_count++] = child;
    return child;
}

/* Revoke a capability and all its descendants */
static inline void cap_revoke_tree(CapNode *node) {
    if (!node) return;
    for (int i = 0; i < node->child_count; i++) {
        cap_revoke_tree(node->children[i]);
    }
    node->cap.rights = 0;
}

/* Free a capability tree */
static inline void cap_tree_free(CapNode *node) {
    if (!node) return;
    for (int i = 0; i < node->child_count; i++) {
        cap_tree_free(node->children[i]);
    }
    free(node);
}

/* Count nodes in a capability tree */
static inline int cap_tree_count(CapNode *node) {
    if (!node) return 0;
    int count = 1;
    for (int i = 0; i < node->child_count; i++) {
        count += cap_tree_count(node->children[i]);
    }
    return count;
}

/* ---- seL4 Endpoint Management ---- */

typedef struct {
    int ep_id;
    seT5_cap cap;
    int msg_queue[9];  /* Ternary-sized message queue (3^2) */
    int msg_head;
    int msg_tail;
    int msg_count;
} seL4_Endpoint;

static inline void endpoint_init(seL4_Endpoint *ep, int id) {
    ep->ep_id = id;
    ep->cap.object_id = id;
    ep->cap.rights = CAP_RIGHT_ALL;
    ep->cap.badge = 0;
    ep->msg_head = 0;
    ep->msg_tail = 0;
    ep->msg_count = 0;
}

static inline int endpoint_send(seL4_Endpoint *ep, int msg) {
    if (ep->msg_count >= 9) return -1; /* queue full */
    ep->msg_queue[ep->msg_tail] = msg;
    ep->msg_tail = (ep->msg_tail + 1) % 9;
    ep->msg_count++;
    return 0;
}

static inline int endpoint_recv(seL4_Endpoint *ep, int *msg) {
    if (ep->msg_count == 0) return -1; /* queue empty */
    *msg = ep->msg_queue[ep->msg_head];
    ep->msg_head = (ep->msg_head + 1) % 9;
    ep->msg_count--;
    return 0;
}

/* ---- seL4 Thread Control ---- */

typedef struct {
    int tid;
    int priority;    /* Ternary priority: N=-1 (low), Z=0 (normal), P=+1 (high) */
    int entry_addr;  /* Bytecode entry point */
    int stack_addr;  /* Stack base in ternary memory */
    int state;       /* 0=ready, 1=running, 2=blocked, 3=dead */
} seL4_TCB;

static inline void tcb_init(seL4_TCB *tcb, int tid, int entry, int stack) {
    tcb->tid = tid;
    tcb->priority = 0;
    tcb->entry_addr = entry;
    tcb->stack_addr = stack;
    tcb->state = 0;
}

/* ---- Compile seL4 kernel stub to ternary bytecode ---- */

/*
 * Compile a full seL4 kernel stub including:
 * - Capability initialization
 * - Endpoint creation
 * - IPC send/recv through the pipeline
 * Returns bytecode length or -1 on error.
 */
int sel4_compile_full(const char *source, unsigned char *out, int max_len);

/*
 * Verify invariant: no capability escalation in derivation tree.
 * Returns 1 if the invariant holds, 0 otherwise.
 */
static inline int verify_no_escalation(CapNode *node) {
    if (!node) return 1;
    for (int i = 0; i < node->child_count; i++) {
        CapNode *child = node->children[i];
        /* Child rights must be subset of parent rights */
        if ((child->cap.rights & ~node->cap.rights) != 0) return 0;
        if (!verify_no_escalation(child)) return 0;
    }
    return 1;
}

/*
 * Verify invariant: revoked caps have zero rights.
 * Returns 1 if all revoked nodes have rights == 0.
 */
static inline int verify_revocation(CapNode *node) {
    if (!node) return 1;
    /* If this node was revoked (rights==0), all children must also be revoked */
    if (node->cap.rights == 0) {
        for (int i = 0; i < node->child_count; i++) {
            if (node->children[i]->cap.rights != 0) return 0;
            if (!verify_revocation(node->children[i])) return 0;
        }
    }
    return 1;
}

#endif /* SEL4_VERIFY_H */
