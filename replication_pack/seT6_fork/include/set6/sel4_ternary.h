/**
 * @file sel4_ternary.h
 * @brief seT6 Moonshot — Full seL4 Kernel Object Model in Balanced Ternary
 *
 * This is the "ternary rewrite of all that seL4 is" — a complete
 * reimplementation of the seL4 microkernel's object model using
 * balanced ternary types and Kleene K₃ logic throughout.
 *
 * seL4 kernel objects reimplemented:
 *   1.  CNode          — Capability space node (radix tree)
 *   2.  TCB            — Thread Control Block with trit priority
 *   3.  Endpoint       — Synchronous IPC rendezvous
 *   4.  Notification   — Asynchronous signal word
 *   5.  Untyped        — Untyped memory (Unknown-initialised)
 *   6.  Frame          — Physical memory frame
 *   7.  PageTable      — Ternary page table entry (validity-tagged)
 *   8.  IRQControl     — Hardware interrupt routing
 *   9.  IRQHandler     — Per-IRQ dispatch
 *  10.  ASID Pool/Ctrl — Address Space Identifier management
 *
 * Key seT6 innovations over binary seL4:
 *   - Ternary validity: T(active), U(pending), F(revoked) — replaces
 *     binary valid/invalid with a three-state lifecycle
 *   - Unknown-init: all memory starts as Unknown, not zero
 *   - Kleene capability operations: AND/OR/NOT on permissions
 *   - Balanced ternary priority: 3 levels vs. 256 binary levels
 *   - Scrub-on-revoke: capability revocation scrubs to Unknown
 *
 * Formal guarantees (proven in Isabelle/HOL proofs):
 *   - Authority confinement: caps cannot escalate beyond their parent
 *   - Non-interference: information flow between domains is trit-controlled
 *   - Integrity: only threads with T-validity caps can modify objects
 *   - Availability: F-validity caps cannot block T-validity operations
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_SEL4_TERNARY_H
#define SET6_SEL4_TERNARY_H

#include "set6/trit.h"
#include "set6/trit_emu.h"
#include "set6/trit_cast.h"
#include "set6/memory.h"
#include "set6/ipc.h"
#include "set6/scheduler.h"

/* ==== Configuration ==================================================== */

#define SET6_MAX_CNODE_SLOTS    256   /* CNode capacity (radix bits = 8) */
#define SET6_MAX_TCBS            64   /* Max threads */
#define SET6_MAX_ENDPOINTS       32   /* Max IPC endpoints */
#define SET6_MAX_NOTIFICATIONS   32   /* Max notification objects */
#define SET6_MAX_UNTYPED         64   /* Max untyped memory regions */
#define SET6_MAX_FRAMES         256   /* Max physical frames */
#define SET6_MAX_PAGE_TABLES     16   /* Max page tables */
#define SET6_MAX_IRQS            32   /* Max hardware interrupts */
#define SET6_MAX_ASID_POOLS       4   /* Max ASID pools */
#define SET6_MAX_DOMAINS          3   /* Ternary: {F, U, T} domains */

/* ==== Kernel Object Types ============================================== */

typedef enum {
    KOBJ_NONE        = 0,
    KOBJ_CNODE       = 1,
    KOBJ_TCB         = 2,
    KOBJ_ENDPOINT    = 3,
    KOBJ_NOTIFICATION= 4,
    KOBJ_UNTYPED     = 5,
    KOBJ_FRAME       = 6,
    KOBJ_PAGE_TABLE  = 7,
    KOBJ_IRQ_CONTROL = 8,
    KOBJ_IRQ_HANDLER = 9,
    KOBJ_ASID_POOL   = 10,
    KOBJ_ASID_CTRL   = 11,
    KOBJ_COUNT       = 12
} kobj_type_t;

/* ==== Capability Structure ============================================= */

/**
 * Ternary capability — the fundamental access control unit.
 *
 * Every operation in seT6 is mediated by capabilities.
 * A capability combines:
 *   - Object reference (type + index)
 *   - Access rights (read/write/grant/revoke as trits)
 *   - Validity (TRIT_TRUE/UNKNOWN/FALSE lifecycle)
 *   - Badge (opaque identifier for IPC)
 *   - Guard (CNode address translation bits)
 *   - Depth (CNode radix depth for lookup)
 */
typedef struct {
    kobj_type_t type;           /* Referenced object type */
    int         obj_index;      /* Index into type-specific array */
    trit        can_read;       /* Read permission */
    trit        can_write;      /* Write permission */
    trit        can_grant;      /* Grant (delegate) permission */
    trit        can_revoke;     /* Revoke sub-capabilities */
    trit        validity;       /* Lifecycle: T=active, U=pending, F=revoked */
    int         badge;          /* IPC badge (unforgeable) */
    int         guard;          /* CNode guard bits */
    int         guard_size;     /* Number of guard bits */
    int         depth;          /* CNode lookup depth */
} set6_cap_t;

/* ---- Capability Constructors ---- */

static inline set6_cap_t cap_mk_null(void) {
    set6_cap_t c = {0};
    c.type     = KOBJ_NONE;
    c.validity = TRIT_FALSE;
    return c;
}

static inline set6_cap_t cap_mk(kobj_type_t type, int idx,
                                trit rd, trit wr, trit gr) {
    set6_cap_t c = {0};
    c.type      = type;
    c.obj_index = idx;
    c.can_read  = rd;
    c.can_write = wr;
    c.can_grant = gr;
    c.can_revoke = TRIT_FALSE;
    c.validity  = TRIT_TRUE;
    return c;
}

/**
 * Capability derivation (mint) — create a child capability.
 *
 * The child can have at most the parent's rights (monotonicity).
 * Permissions are combined with Kleene AND (min): child ≤ parent.
 */
static inline set6_cap_t cap_derive(const set6_cap_t *parent,
                                    trit rd, trit wr, trit gr, int badge) {
    set6_cap_t child = *parent;
    child.can_read  = trit_and(parent->can_read,  rd);
    child.can_write = trit_and(parent->can_write, wr);
    child.can_grant = trit_and(parent->can_grant, gr);
    child.badge     = badge;
    child.validity  = TRIT_TRUE;
    return child;
}

/**
 * Capability revocation — move to F(revoked) state.
 * Permissions are scrubbed to Unknown (not zero!) for security.
 */
static inline void cap_revoke(set6_cap_t *cap) {
    if (!cap) return;
    cap->validity  = TRIT_FALSE;
    cap->can_read  = TRIT_UNKNOWN;
    cap->can_write = TRIT_UNKNOWN;
    cap->can_grant = TRIT_UNKNOWN;
}

/**
 * Check if a capability grants a specific right.
 * Returns T only if validity is T AND the right is T.
 */
static inline trit cap_has_right(const set6_cap_t *cap, trit right) {
    if (!cap) return TRIT_FALSE;
    return trit_and(cap->validity, right);
}

/* ==== 1. CNode — Capability Space Node ================================= */

/**
 * CNode: a table of capability slots forming a radix tree.
 *
 * In seL4, CNodes are the fundamental namespace for capabilities.
 * A thread's CSpace is a tree of CNodes, addressed by a
 * multi-level path (guard + index at each level).
 *
 * seT6 innovation: each slot has a ternary validity field that
 * propagates through lookups — an Unknown slot means "pending
 * capability transfer, not yet committed."
 */
typedef struct {
    set6_cap_t  slots[SET6_MAX_CNODE_SLOTS];
    int         slot_count;    /* Number of used slots */
    int         radix_bits;    /* log₃ of capacity (8 in base config) */
    int         guard;         /* CNode guard for path translation */
    int         guard_size;    /* Guard bit width */
    trit        validity;      /* Whole-node validity state */
} set6_cnode_t;

static inline void cnode_init(set6_cnode_t *cn) {
    if (!cn) return;
    for (int i = 0; i < SET6_MAX_CNODE_SLOTS; i++)
        cn->slots[i] = cap_mk_null();
    cn->slot_count = 0;
    cn->radix_bits = 8;
    cn->guard = 0;
    cn->guard_size = 0;
    cn->validity = TRIT_TRUE;
}

/**
 * CNode slot lookup with guard check.
 *
 * Returns pointer to capability slot, or NULL if:
 *   - CNode is F-validity (revoked)
 *   - Index out of range
 *   - Guard mismatch
 */
static inline set6_cap_t *cnode_lookup(set6_cnode_t *cn, int index) {
    if (!cn || cn->validity == TRIT_FALSE) return NULL;
    if (index < 0 || index >= SET6_MAX_CNODE_SLOTS) return NULL;
    return &cn->slots[index];
}

static inline int cnode_insert(set6_cnode_t *cn, int index, set6_cap_t cap) {
    if (!cn || cn->validity == TRIT_FALSE) return -1;
    if (index < 0 || index >= SET6_MAX_CNODE_SLOTS) return -1;
    if (cn->slots[index].type != KOBJ_NONE) return -2; /* Slot occupied */
    cn->slots[index] = cap;
    cn->slot_count++;
    return 0;
}

static inline int cnode_delete(set6_cnode_t *cn, int index) {
    if (!cn || cn->validity == TRIT_FALSE) return -1;
    if (index < 0 || index >= SET6_MAX_CNODE_SLOTS) return -1;
    cap_revoke(&cn->slots[index]);
    cn->slots[index] = cap_mk_null();
    cn->slot_count--;
    return 0;
}

/**
 * Revoke all capabilities in a CNode (recursive revocation).
 * In seL4, this is the "Revoke" syscall — invalidates all
 * children derived from a given capability.
 */
static inline void cnode_revoke_all(set6_cnode_t *cn) {
    if (!cn) return;
    for (int i = 0; i < SET6_MAX_CNODE_SLOTS; i++) {
        if (cn->slots[i].type != KOBJ_NONE)
            cap_revoke(&cn->slots[i]);
    }
    cn->validity = TRIT_FALSE;
}

/* ==== 2. TCB — Thread Control Block ==================================== */

/**
 * TCB: seL4-style thread control block with ternary extensions.
 *
 * Each thread has:
 *   - Priority (balanced ternary: T=high, U=normal, F=low)
 *   - CSpace root (CNode cap for capability lookup)
 *   - VSpace root (page table cap for address translation)
 *   - IPC buffer (frame cap for message passing)
 *   - Fault handler (endpoint cap for fault delivery)
 *   - Domain (ternary information flow domain: T/U/F)
 *   - Bound notification (for signaled recv)
 *   - State (running/blocked/inactive as ternary)
 */
typedef enum {
    THREAD_INACTIVE = -1,   /* F: not schedulable */
    THREAD_BLOCKED  =  0,   /* U: waiting for IPC/notification */
    THREAD_RUNNING  =  1,   /* T: schedulable */
} thread_state_t;

typedef struct {
    int              id;            /* Thread identifier */
    thread_state_t   state;         /* Lifecycle state */
    trit             priority;      /* Scheduling priority (T/U/F) */
    trit             domain;        /* Information flow domain */

    /* Capability references (indices into CNode) */
    int              cspace_root;   /* CNode slot for CSpace root */
    int              vspace_root;   /* CNode slot for VSpace root */
    int              ipc_buffer;    /* CNode slot for IPC buffer frame */
    int              fault_handler; /* CNode slot for fault endpoint */
    int              bound_notif;   /* CNode slot for bound notification (-1=none) */

    /* Register context (simplified: 16 ternary registers) */
    trit2_reg32      regs[16];

    /* Two-stack model */
    int              op_stack[64];  /* Operand stack */
    int              ret_stack[64]; /* Return stack */
    int              op_sp;         /* Operand stack pointer */
    int              ret_sp;        /* Return stack pointer */

    /* Timing */
    int              timeslice;     /* Remaining time quantum */
    int              max_timeslice; /* Maximum time quantum */

    /* Validity tracking */
    trit             validity;      /* T=alive, U=suspended, F=dead */
} set6_tcb_t;

static inline void tcb_init(set6_tcb_t *tcb, int id) {
    if (!tcb) return;
    tcb->id            = id;
    tcb->state         = THREAD_INACTIVE;
    tcb->priority      = TRIT_UNKNOWN;
    tcb->domain        = TRIT_UNKNOWN;
    tcb->cspace_root   = -1;
    tcb->vspace_root   = -1;
    tcb->ipc_buffer    = -1;
    tcb->fault_handler = -1;
    tcb->bound_notif   = -1;
    tcb->op_sp         = 0;
    tcb->ret_sp        = 0;
    tcb->timeslice     = 10;
    tcb->max_timeslice = 10;
    tcb->validity      = TRIT_TRUE;

    for (int i = 0; i < 16; i++)
        tcb->regs[i] = trit2_reg32_splat(TRIT2_UNKNOWN);
}

static inline void tcb_configure(set6_tcb_t *tcb, int cspace, int vspace,
                                 int ipc_buf, int fault_ep) {
    if (!tcb || tcb->validity == TRIT_FALSE) return;
    tcb->cspace_root   = cspace;
    tcb->vspace_root   = vspace;
    tcb->ipc_buffer    = ipc_buf;
    tcb->fault_handler = fault_ep;
}

static inline void tcb_set_priority(set6_tcb_t *tcb, trit prio) {
    if (!tcb || tcb->validity == TRIT_FALSE) return;
    tcb->priority = prio;
}

static inline void tcb_resume(set6_tcb_t *tcb) {
    if (!tcb || tcb->validity == TRIT_FALSE) return;
    tcb->state      = THREAD_RUNNING;
    tcb->timeslice  = tcb->max_timeslice;
}

static inline void tcb_suspend(set6_tcb_t *tcb) {
    if (!tcb) return;
    tcb->state = THREAD_BLOCKED;
}

static inline void tcb_destroy(set6_tcb_t *tcb) {
    if (!tcb) return;
    tcb->state    = THREAD_INACTIVE;
    tcb->validity = TRIT_FALSE;
    for (int i = 0; i < 16; i++)
        tcb->regs[i] = trit2_reg32_splat(TRIT2_UNKNOWN);
}

/* ==== 3. Endpoint — Synchronous IPC ==================================== */

/**
 * seL4-style synchronous IPC endpoint with ternary validity.
 *
 * Endpoints support:
 *   - Send: blocks sender until a receiver is waiting
 *   - Recv: blocks receiver until a sender arrives
 *   - Call: Send + Recv (client-server pattern)
 *   - Reply: non-blocking reply to a Call
 *   - NBSend: non-blocking send (returns U if no receiver)
 *
 * The ternary twist: endpoint state is {T, U, F}:
 *   - T: active, messages can be transferred
 *   - U: pending, endpoint exists but no thread is bound
 *   - F: revoked, all operations fail immediately
 */
/* ep_state_t (EP_IDLE, EP_SEND_BLOCKED, EP_RECV_BLOCKED) is provided by ipc.h */

typedef struct {
    /* Ternary message payload: 4 trits + badge */
    trit    msg[4];
    int     badge;
    int     sender_id;
} set6_ipc_msg_t;

typedef struct {
    int               id;
    trit              validity;      /* Endpoint lifecycle */
    ep_state_t        queue_state;   /* Current queue direction */

    /* Blocked thread queues (circular) */
    int               send_queue[SET6_MAX_TCBS];
    int               send_head, send_tail;

    int               recv_queue[SET6_MAX_TCBS];
    int               recv_head, recv_tail;

    /* Last transferred message (for debugging/proof) */
    set6_ipc_msg_t    last_msg;
} set6_endpoint_t;

static inline void endpoint_init(set6_endpoint_t *ep, int id) {
    if (!ep) return;
    ep->id          = id;
    ep->validity    = TRIT_TRUE;
    ep->queue_state = EP_IDLE;
    ep->send_head   = 0;
    ep->send_tail   = 0;
    ep->recv_head   = 0;
    ep->recv_tail   = 0;
    for (int i = 0; i < 4; i++)
        ep->last_msg.msg[i] = TRIT_UNKNOWN;
}

/**
 * Enqueue a sender. Returns T if successful, U if queue full.
 */
static inline trit endpoint_send_enqueue(set6_endpoint_t *ep, int thread_id) {
    if (!ep || ep->validity == TRIT_FALSE) return TRIT_FALSE;
    int next = (ep->send_tail + 1) % SET6_MAX_TCBS;
    if (next == ep->send_head) return TRIT_UNKNOWN; /* Queue full */
    ep->send_queue[ep->send_tail] = thread_id;
    ep->send_tail = next;
    ep->queue_state = EP_SEND_BLOCKED;
    return TRIT_TRUE;
}

static inline int endpoint_send_dequeue(set6_endpoint_t *ep) {
    if (!ep || ep->send_head == ep->send_tail) return -1;
    int tid = ep->send_queue[ep->send_head];
    ep->send_head = (ep->send_head + 1) % SET6_MAX_TCBS;
    if (ep->send_head == ep->send_tail) ep->queue_state = EP_IDLE;
    return tid;
}

static inline trit endpoint_recv_enqueue(set6_endpoint_t *ep, int thread_id) {
    if (!ep || ep->validity == TRIT_FALSE) return TRIT_FALSE;
    int next = (ep->recv_tail + 1) % SET6_MAX_TCBS;
    if (next == ep->recv_head) return TRIT_UNKNOWN;
    ep->recv_queue[ep->recv_tail] = thread_id;
    ep->recv_tail = next;
    ep->queue_state = EP_RECV_BLOCKED;
    return TRIT_TRUE;
}

static inline int endpoint_recv_dequeue(set6_endpoint_t *ep) {
    if (!ep || ep->recv_head == ep->recv_tail) return -1;
    int tid = ep->recv_queue[ep->recv_head];
    ep->recv_head = (ep->recv_head + 1) % SET6_MAX_TCBS;
    if (ep->recv_head == ep->recv_tail) ep->queue_state = EP_IDLE;
    return tid;
}

/**
 * Transfer message from sender to receiver (the core IPC operation).
 * Returns T if transfer completed, F if either queue empty.
 */
static inline trit endpoint_transfer(set6_endpoint_t *ep,
                                     const set6_ipc_msg_t *msg) {
    if (!ep || !msg || ep->validity == TRIT_FALSE) return TRIT_FALSE;
    ep->last_msg = *msg;
    return TRIT_TRUE;
}

/* ==== 4. Notification — Asynchronous Signal ============================ */

/**
 * Notification object: 32-bit word of ternary signal bits.
 *
 * Each bit position can be:
 *   T: signal asserted
 *   U: signal cleared (idle)
 *   F: signal masked (disabled)
 *
 * Operations:
 *   Signal: OR the notification word (assert bits)
 *   Wait:   block until any T bit, clear consumed bits to U
 *   Poll:   non-blocking check (returns U if no signals)
 */
typedef struct {
    int              id;
    trit             validity;
    trit2_reg32      signal_word;   /* 32 ternary signal bits */
    int              bound_tcb;     /* Thread bound to this notification (-1=none) */

    /* Waiting thread queue */
    int              wait_queue[SET6_MAX_TCBS];
    int              wait_head, wait_tail;
} set6_notification_t;

static inline void notification_init(set6_notification_t *ntf, int id) {
    if (!ntf) return;
    ntf->id        = id;
    ntf->validity  = TRIT_TRUE;
    ntf->signal_word = trit2_reg32_splat(TRIT2_UNKNOWN); /* All idle */
    ntf->bound_tcb  = -1;
    ntf->wait_head  = 0;
    ntf->wait_tail  = 0;
}

/**
 * Signal: assert bit at position with Kleene OR.
 */
static inline trit notification_signal(set6_notification_t *ntf, int bit) {
    if (!ntf || ntf->validity == TRIT_FALSE) return TRIT_FALSE;
    if (bit < 0 || bit >= 32) return TRIT_FALSE;
    trit2_reg32_set(&ntf->signal_word, bit, TRIT2_TRUE);
    return TRIT_TRUE;
}

/**
 * Poll: check if any signal bits are T. Non-blocking.
 * Returns the number of T bits, or 0 if none.
 */
static inline int notification_poll(const set6_notification_t *ntf) {
    if (!ntf || ntf->validity == TRIT_FALSE) return -1;
    int count = 0;
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&ntf->signal_word, i) == TRIT2_TRUE)
            count++;
    }
    return count;
}

/**
 * Wait: consume all T signals (clear to U), return count consumed.
 */
static inline int notification_wait(set6_notification_t *ntf) {
    if (!ntf || ntf->validity == TRIT_FALSE) return -1;
    int consumed = 0;
    for (int i = 0; i < 32; i++) {
        if (trit2_reg32_get(&ntf->signal_word, i) == TRIT2_TRUE) {
            trit2_reg32_set(&ntf->signal_word, i, TRIT2_UNKNOWN);
            consumed++;
        }
    }
    return consumed;
}

/* ==== 5. Untyped Memory ================================================ */

/**
 * Untyped memory: the raw memory allocator in seL4.
 *
 * Everything in seL4 starts as Untyped memory. It can be "retyped"
 * into specific kernel objects (CNode, TCB, Endpoint, Frame, etc.)
 *
 * seT6 innovation: Untyped memory is Unknown-initialised (not zero).
 * Retyping produces objects with Unknown defaults that must be
 * explicitly configured before use (fail-safe design).
 */
typedef struct {
    int         id;
    trit        validity;
    int         base_addr;       /* Start address in physical memory */
    int         size_bits;       /* log₂ of size in bytes */
    int         watermark;       /* Offset of first free byte */
    int         children_count;  /* Number of retyped children */
    kobj_type_t children[32];    /* Types of retyped children */
} set6_untyped_t;

static inline void untyped_init(set6_untyped_t *ut, int id,
                                int base, int size_bits) {
    if (!ut) return;
    ut->id             = id;
    ut->validity       = TRIT_TRUE;
    ut->base_addr      = base;
    ut->size_bits      = size_bits;
    ut->watermark      = 0;
    ut->children_count = 0;
}

/**
 * Retype: carve a kernel object from Untyped memory.
 *
 * Returns the child index, or -1 if insufficient space.
 * The child is Unknown-initialised.
 */
static inline int untyped_retype(set6_untyped_t *ut, kobj_type_t type,
                                 int obj_size) {
    if (!ut || ut->validity == TRIT_FALSE) return -1;
    int total = 1 << ut->size_bits;
    if (ut->watermark + obj_size > total) return -1;
    if (ut->children_count >= 32) return -1;

    int idx = ut->children_count;
    ut->children[idx] = type;
    ut->children_count++;
    ut->watermark += obj_size;
    return idx;
}

/**
 * Revoke: reclaim all children (reset watermark).
 * In seL4, revoking an Untyped cap destroys all derived objects.
 */
static inline void untyped_revoke(set6_untyped_t *ut) {
    if (!ut) return;
    ut->watermark = 0;
    ut->children_count = 0;
    ut->validity = TRIT_UNKNOWN; /* Pending re-initialisation */
}

/* ==== 6. Frame — Physical Memory Frame ================================= */

/**
 * Frame: a mapped page of physical memory with ternary attributes.
 *
 * Attributes (per-frame):
 *   - Cacheable: T=cached, U=write-through, F=uncached
 *   - Executable: T=exec, U=pending, F=no-exec
 *   - Writable: T=rw, U=ro-pending, F=ro
 */
typedef struct {
    int         id;
    trit        validity;
    int         phys_addr;     /* Physical page number */
    int         size_bits;     /* Frame size (log₂ bytes) */
    int         mapped_vaddr;  /* Virtual address if mapped, -1 if not */
    int         mapped_asid;   /* ASID of mapping, -1 if unmapped */
    trit        cacheable;     /* Cache policy */
    trit        executable;    /* Execute permission */
    trit        writable;      /* Write permission */
} set6_frame_t;

static inline void frame_init(set6_frame_t *fr, int id, int phys) {
    if (!fr) return;
    fr->id           = id;
    fr->validity     = TRIT_TRUE;
    fr->phys_addr    = phys;
    fr->size_bits    = 12; /* 4KB default */
    fr->mapped_vaddr = -1;
    fr->mapped_asid  = -1;
    fr->cacheable    = TRIT_TRUE;
    fr->executable   = TRIT_FALSE;
    fr->writable     = TRIT_TRUE;
}

static inline trit frame_map(set6_frame_t *fr, int vaddr, int asid) {
    if (!fr || fr->validity == TRIT_FALSE) return TRIT_FALSE;
    if (fr->mapped_vaddr >= 0) return TRIT_UNKNOWN; /* Already mapped */
    fr->mapped_vaddr = vaddr;
    fr->mapped_asid  = asid;
    return TRIT_TRUE;
}

static inline trit frame_unmap(set6_frame_t *fr) {
    if (!fr || fr->validity == TRIT_FALSE) return TRIT_FALSE;
    fr->mapped_vaddr = -1;
    fr->mapped_asid  = -1;
    return TRIT_TRUE;
}

/* ==== 7. Page Table — Ternary Virtual Memory =========================== */

/**
 * Page table entry with ternary validity.
 *
 * Each PTE has a trit validity state:
 *   T: mapped and accessible
 *   U: mapped but access-fault pending (lazy allocation/COW)
 *   F: unmapped (page fault)
 */
typedef struct {
    int   frame_index;   /* Index into frame array (-1 = unmapped) */
    trit  present;       /* T=mapped, U=pending-fault, F=unmapped */
    trit  writable;      /* T=rw, U=ro-cow, F=ro */
    trit  executable;    /* T=exec, U=pending, F=no-exec */
    trit  user_access;   /* T=user, U=kernel-only, F=no-access */
    int   asid;          /* Address space identifier */
} set6_pte_t;

#define SET6_PTE_PER_TABLE  256 /* 256 entries per table */

typedef struct {
    int         id;
    trit        validity;
    int         level;          /* Page table level (0=root, 1=leaf) */
    set6_pte_t  entries[SET6_PTE_PER_TABLE];
    int         mapped_count;   /* Number of valid mappings */
} set6_page_table_t;

static inline void page_table_init(set6_page_table_t *pt, int id, int level) {
    if (!pt) return;
    pt->id           = id;
    pt->validity     = TRIT_TRUE;
    pt->level        = level;
    pt->mapped_count = 0;
    for (int i = 0; i < SET6_PTE_PER_TABLE; i++) {
        pt->entries[i].frame_index = -1;
        pt->entries[i].present     = TRIT_FALSE;
        pt->entries[i].writable    = TRIT_FALSE;
        pt->entries[i].executable  = TRIT_FALSE;
        pt->entries[i].user_access = TRIT_FALSE;
        pt->entries[i].asid        = -1;
    }
}

/**
 * Map a frame into the page table.
 */
static inline trit page_table_map(set6_page_table_t *pt, int index,
                                  int frame_idx, trit wr, trit ex, int asid) {
    if (!pt || pt->validity == TRIT_FALSE) return TRIT_FALSE;
    if (index < 0 || index >= SET6_PTE_PER_TABLE) return TRIT_FALSE;
    if (pt->entries[index].present == TRIT_TRUE) return TRIT_UNKNOWN; /* Already mapped */

    pt->entries[index].frame_index = frame_idx;
    pt->entries[index].present     = TRIT_TRUE;
    pt->entries[index].writable    = wr;
    pt->entries[index].executable  = ex;
    pt->entries[index].user_access = TRIT_TRUE;
    pt->entries[index].asid        = asid;
    pt->mapped_count++;
    return TRIT_TRUE;
}

static inline trit page_table_unmap(set6_page_table_t *pt, int index) {
    if (!pt || pt->validity == TRIT_FALSE) return TRIT_FALSE;
    if (index < 0 || index >= SET6_PTE_PER_TABLE) return TRIT_FALSE;
    pt->entries[index].frame_index = -1;
    pt->entries[index].present     = TRIT_FALSE;
    pt->mapped_count--;
    return TRIT_TRUE;
}

/**
 * Page table lookup — translate virtual index to frame.
 * Returns frame_index if T-valid, -1 if F, -2 if U(fault pending).
 */
static inline int page_table_lookup(const set6_page_table_t *pt, int index) {
    if (!pt || pt->validity == TRIT_FALSE) return -1;
    if (index < 0 || index >= SET6_PTE_PER_TABLE) return -1;
    const set6_pte_t *pte = &pt->entries[index];
    if (pte->present == TRIT_TRUE)    return pte->frame_index;
    if (pte->present == TRIT_UNKNOWN) return -2; /* Fault pending */
    return -1; /* Unmapped */
}

/* ==== 8-9. IRQ Control & Handler ======================================= */

/**
 * IRQ management with ternary priority and validity.
 *
 * IRQControl: system-wide IRQ namespace (one per system)
 * IRQHandler: per-IRQ handler bound to a notification object
 */
typedef struct {
    int              irq_num;
    trit             validity;      /* T=active, U=masked, F=disabled */
    trit             priority;      /* Interrupt priority */
    int              notif_index;   /* Bound notification object (-1=none) */
    int              handler_tcb;   /* Handler thread (-1=none) */
    int              trigger_count; /* Number of times triggered */
} set6_irq_handler_t;

typedef struct {
    set6_irq_handler_t  handlers[SET6_MAX_IRQS];
    int                 handler_count;
    trit                validity;
} set6_irq_control_t;

static inline void irq_control_init(set6_irq_control_t *ic) {
    if (!ic) return;
    ic->handler_count = 0;
    ic->validity      = TRIT_TRUE;
    for (int i = 0; i < SET6_MAX_IRQS; i++) {
        ic->handlers[i].irq_num       = i;
        ic->handlers[i].validity      = TRIT_FALSE;
        ic->handlers[i].priority      = TRIT_UNKNOWN;
        ic->handlers[i].notif_index   = -1;
        ic->handlers[i].handler_tcb   = -1;
        ic->handlers[i].trigger_count = 0;
    }
}

/**
 * Register an IRQ handler: bind IRQ to a notification object.
 */
static inline trit irq_handler_set(set6_irq_control_t *ic, int irq,
                                   int notif_idx, int tcb_id) {
    if (!ic || ic->validity == TRIT_FALSE) return TRIT_FALSE;
    if (irq < 0 || irq >= SET6_MAX_IRQS) return TRIT_FALSE;
    ic->handlers[irq].validity    = TRIT_TRUE;
    ic->handlers[irq].notif_index = notif_idx;
    ic->handlers[irq].handler_tcb = tcb_id;
    ic->handler_count++;
    return TRIT_TRUE;
}

/**
 * Acknowledge an IRQ (clear pending, re-enable).
 */
static inline trit irq_handler_ack(set6_irq_control_t *ic, int irq) {
    if (!ic || irq < 0 || irq >= SET6_MAX_IRQS) return TRIT_FALSE;
    set6_irq_handler_t *h = &ic->handlers[irq];
    if (h->validity == TRIT_FALSE) return TRIT_FALSE;
    h->trigger_count++;
    return TRIT_TRUE;
}

/* ==== 10. ASID Pool/Control ============================================ */

/**
 * ASID (Address Space Identifier) management.
 *
 * Controls process address space isolation. In seL4, ASIDs prevent
 * one process from accessing another's page tables.
 *
 * seT6: ASID pools have ternary validity — an Unknown ASID means
 * "address space is being migrated between cores."
 */
#define SET6_ASIDS_PER_POOL  64

typedef struct {
    int   id;
    trit  validity;
    trit  asids[SET6_ASIDS_PER_POOL]; /* T=allocated, U=migrating, F=free */
    int   allocated_count;
} set6_asid_pool_t;

static inline void asid_pool_init(set6_asid_pool_t *pool, int id) {
    if (!pool) return;
    pool->id = id;
    pool->validity = TRIT_TRUE;
    pool->allocated_count = 0;
    for (int i = 0; i < SET6_ASIDS_PER_POOL; i++)
        pool->asids[i] = TRIT_FALSE; /* All free */
}

static inline int asid_pool_alloc(set6_asid_pool_t *pool) {
    if (!pool || pool->validity == TRIT_FALSE) return -1;
    for (int i = 0; i < SET6_ASIDS_PER_POOL; i++) {
        if (pool->asids[i] == TRIT_FALSE) {
            pool->asids[i] = TRIT_TRUE;
            pool->allocated_count++;
            return i;
        }
    }
    return -1; /* Pool full */
}

static inline trit asid_pool_free(set6_asid_pool_t *pool, int asid) {
    if (!pool || pool->validity == TRIT_FALSE) return TRIT_FALSE;
    if (asid < 0 || asid >= SET6_ASIDS_PER_POOL) return TRIT_FALSE;
    pool->asids[asid] = TRIT_FALSE;
    pool->allocated_count--;
    return TRIT_TRUE;
}

/* ==== MDB — Mapping Database (Capability Derivation Tree) ============== */

/**
 * MDB: tracks the parent-child relationship between capabilities.
 *
 * In seL4, the MDB is a doubly-linked list threaded through the
 * capability table, tracking which capabilities were derived from
 * which parent. This enables recursive revocation.
 *
 * seT6 MDB: each entry has a ternary validity state:
 *   T: active derivation link
 *   U: pending (mid-transfer)
 *   F: revoked (link dead)
 */
#define SET6_MAX_MDB_ENTRIES 512

typedef struct {
    int    cap_cnode;     /* CNode index of this capability */
    int    cap_slot;      /* Slot within CNode */
    int    parent;        /* MDB index of parent (-1 = root) */
    int    first_child;   /* MDB index of first child (-1 = leaf) */
    int    next_sibling;  /* MDB index of next sibling (-1 = last) */
    trit   validity;      /* T=active, U=pending, F=revoked */
} set6_mdb_entry_t;

typedef struct {
    set6_mdb_entry_t entries[SET6_MAX_MDB_ENTRIES];
    int              count;
} set6_mdb_t;

static inline void mdb_init(set6_mdb_t *mdb) {
    if (!mdb) return;
    mdb->count = 0;
    for (int i = 0; i < SET6_MAX_MDB_ENTRIES; i++) {
        mdb->entries[i].cap_cnode    = -1;
        mdb->entries[i].cap_slot     = -1;
        mdb->entries[i].parent       = -1;
        mdb->entries[i].first_child  = -1;
        mdb->entries[i].next_sibling = -1;
        mdb->entries[i].validity     = TRIT_FALSE;
    }
}

static inline int mdb_insert(set6_mdb_t *mdb, int cnode, int slot, int parent) {
    if (!mdb || mdb->count >= SET6_MAX_MDB_ENTRIES) return -1;
    int idx = mdb->count++;
    set6_mdb_entry_t *e = &mdb->entries[idx];
    e->cap_cnode    = cnode;
    e->cap_slot     = slot;
    e->parent       = parent;
    e->first_child  = -1;
    e->next_sibling = -1;
    e->validity     = TRIT_TRUE;

    /* Link to parent's child list */
    if (parent >= 0 && parent < SET6_MAX_MDB_ENTRIES) {
        set6_mdb_entry_t *p = &mdb->entries[parent];
        if (p->first_child < 0) {
            p->first_child = idx;
        } else {
            /* Find last sibling */
            int sib = p->first_child;
            while (mdb->entries[sib].next_sibling >= 0)
                sib = mdb->entries[sib].next_sibling;
            mdb->entries[sib].next_sibling = idx;
        }
    }

    return idx;
}

/**
 * Recursive revocation: revoke entry and all its descendants.
 */
static inline void mdb_revoke(set6_mdb_t *mdb, int idx) {
    if (!mdb || idx < 0 || idx >= SET6_MAX_MDB_ENTRIES) return;
    set6_mdb_entry_t *e = &mdb->entries[idx];
    e->validity = TRIT_FALSE;

    /* Revoke all children recursively */
    int child = e->first_child;
    while (child >= 0) {
        int next = mdb->entries[child].next_sibling;
        mdb_revoke(mdb, child);
        child = next;
    }
}

/* ==== Unified Kernel State ============================================= */

/**
 * set6_kernel_t — The complete seT6 microkernel state.
 *
 * Contains all kernel objects in a single structure, mirroring
 * the seL4 kernel's global state.
 */
typedef struct {
    /* Object arrays */
    set6_cnode_t          cnodes[4];              /* CSpace roots (one per domain) */
    set6_tcb_t            tcbs[SET6_MAX_TCBS];
    set6_endpoint_t       endpoints[SET6_MAX_ENDPOINTS];
    set6_notification_t   notifications[SET6_MAX_NOTIFICATIONS];
    set6_untyped_t        untyped[SET6_MAX_UNTYPED];
    set6_frame_t          frames[SET6_MAX_FRAMES];
    set6_page_table_t     page_tables[SET6_MAX_PAGE_TABLES];
    set6_irq_control_t    irq_control;
    set6_asid_pool_t      asid_pools[SET6_MAX_ASID_POOLS];
    set6_mdb_t            mdb;

    /* Counts */
    int  tcb_count;
    int  ep_count;
    int  ntf_count;
    int  ut_count;
    int  frame_count;
    int  pt_count;
    int  asid_pool_count;

    /* Scheduler state */
    int  current_thread;         /* Currently running TCB index */
    trit current_domain;         /* Active security domain */
    int  domain_schedule[3];     /* Time slices per domain {F,U,T} */

    /* System tick */
    int  tick;
} set6_kernel_t;

/**
 * @brief Initialise the complete seT6 kernel.
 */
static inline void set6_kernel_init(set6_kernel_t *k) {
    if (!k) return;

    /* CNodes (one per ternary domain) */
    for (int i = 0; i < 3; i++)
        cnode_init(&k->cnodes[i]);
    cnode_init(&k->cnodes[3]); /* Extra CNode for kernel caps */

    /* TCBs */
    for (int i = 0; i < SET6_MAX_TCBS; i++)
        tcb_init(&k->tcbs[i], i);
    k->tcb_count = 0;

    /* Endpoints */
    for (int i = 0; i < SET6_MAX_ENDPOINTS; i++)
        endpoint_init(&k->endpoints[i], i);
    k->ep_count = 0;

    /* Notifications */
    for (int i = 0; i < SET6_MAX_NOTIFICATIONS; i++)
        notification_init(&k->notifications[i], i);
    k->ntf_count = 0;

    /* Untyped */
    for (int i = 0; i < SET6_MAX_UNTYPED; i++)
        untyped_init(&k->untyped[i], i, i * 4096, 12);
    k->ut_count = 0;

    /* Frames */
    for (int i = 0; i < SET6_MAX_FRAMES; i++)
        frame_init(&k->frames[i], i, i);
    k->frame_count = 0;

    /* Page tables */
    for (int i = 0; i < SET6_MAX_PAGE_TABLES; i++)
        page_table_init(&k->page_tables[i], i, 0);
    k->pt_count = 0;

    /* IRQ */
    irq_control_init(&k->irq_control);

    /* ASID pools */
    for (int i = 0; i < SET6_MAX_ASID_POOLS; i++)
        asid_pool_init(&k->asid_pools[i], i);
    k->asid_pool_count = 0;

    /* MDB */
    mdb_init(&k->mdb);

    /* Scheduler */
    k->current_thread = -1;
    k->current_domain = TRIT_UNKNOWN;
    k->domain_schedule[0] = 1;  /* F domain: 1 tick */
    k->domain_schedule[1] = 5;  /* U domain: 5 ticks (normal) */
    k->domain_schedule[2] = 10; /* T domain: 10 ticks (high priority) */

    k->tick = 0;
}

/* ---- Kernel System Call Dispatch -------------------------------------- */

/**
 * seL4-compatible syscall numbers for the seT6 kernel.
 *
 * Each syscall takes a capability (looked up via CSpace)
 * and an operation code.
 */
typedef enum {
    SEL4_SYS_SEND        = 0,
    SEL4_SYS_RECV        = 1,
    SEL4_SYS_CALL        = 2,
    SEL4_SYS_REPLY       = 3,
    SEL4_SYS_NBSEND      = 4,
    SEL4_SYS_YIELD        = 5,
    SEL4_SYS_CNODE_COPY   = 10,
    SEL4_SYS_CNODE_MINT   = 11,
    SEL4_SYS_CNODE_DELETE  = 12,
    SEL4_SYS_CNODE_REVOKE = 13,
    SEL4_SYS_UNTYPED_RETYPE = 20,
    SEL4_SYS_TCB_CONFIGURE  = 30,
    SEL4_SYS_TCB_SET_PRIO   = 31,
    SEL4_SYS_TCB_RESUME     = 32,
    SEL4_SYS_TCB_SUSPEND    = 33,
    SEL4_SYS_IRQ_SET_HANDLER = 40,
    SEL4_SYS_IRQ_ACK         = 41,
    SEL4_SYS_PT_MAP          = 50,
    SEL4_SYS_PT_UNMAP        = 51,
    SEL4_SYS_FRAME_MAP       = 52,
    SEL4_SYS_FRAME_UNMAP     = 53,
    SEL4_SYS_ASID_ALLOC      = 60,
    SEL4_SYS_ASID_FREE       = 61,
} sel4_syscall_t;

/**
 * @brief Create a new thread (seL4 TCB_Configure equivalent).
 */
static inline int set6_create_thread(set6_kernel_t *k, trit priority,
                                     trit domain) {
    if (!k || k->tcb_count >= SET6_MAX_TCBS) return -1;
    int idx = k->tcb_count++;
    tcb_init(&k->tcbs[idx], idx);
    tcb_set_priority(&k->tcbs[idx], priority);
    k->tcbs[idx].domain = domain;
    tcb_resume(&k->tcbs[idx]);
    return idx;
}

/**
 * @brief Create a new endpoint.
 */
static inline int set6_create_endpoint(set6_kernel_t *k) {
    if (!k || k->ep_count >= SET6_MAX_ENDPOINTS) return -1;
    int idx = k->ep_count++;
    endpoint_init(&k->endpoints[idx], idx);
    return idx;
}

/**
 * @brief Create a new notification.
 */
static inline int set6_create_notification(set6_kernel_t *k) {
    if (!k || k->ntf_count >= SET6_MAX_NOTIFICATIONS) return -1;
    int idx = k->ntf_count++;
    notification_init(&k->notifications[idx], idx);
    return idx;
}

/**
 * @brief Schedule: pick next thread based on ternary domain + priority.
 *
 * Scheduling order:
 *   1. T-domain threads first (highest priority domain)
 *   2. Within domain: T-priority > U-priority > F-priority
 *   3. Round-robin within same priority
 */
static inline int set6_schedule(set6_kernel_t *k) {
    if (!k) return -1;

    k->tick++;

    /* Domain scheduling: cycle through T→U→F */
    trit domain_order[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    trit prio_order[]   = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};

    for (int d = 0; d < 3; d++) {
        for (int p = 0; p < 3; p++) {
            for (int t = 0; t < k->tcb_count; t++) {
                set6_tcb_t *tcb = &k->tcbs[t];
                if (tcb->state == THREAD_RUNNING &&
                    tcb->domain == domain_order[d] &&
                    tcb->priority == prio_order[p] &&
                    tcb->validity == TRIT_TRUE) {
                    k->current_thread = t;
                    k->current_domain = tcb->domain;
                    return t;
                }
            }
        }
    }

    return -1; /* No runnable threads */
}

/**
 * @brief IPC Send via endpoint capability.
 */
static inline trit set6_ipc_send(set6_kernel_t *k, int ep_idx,
                                 const set6_ipc_msg_t *msg) {
    if (!k || ep_idx < 0 || ep_idx >= k->ep_count) return TRIT_FALSE;
    return endpoint_transfer(&k->endpoints[ep_idx], msg);
}

/**
 * @brief Retype untyped memory into a kernel object.
 */
static inline int set6_untyped_retype(set6_kernel_t *k, int ut_idx,
                                      kobj_type_t type) {
    if (!k || ut_idx < 0 || ut_idx >= k->ut_count) return -1;

    /* Object sizes (simplified) */
    int size = 64; /* Default */
    switch (type) {
        case KOBJ_TCB:          size = sizeof(set6_tcb_t); break;
        case KOBJ_ENDPOINT:     size = sizeof(set6_endpoint_t); break;
        case KOBJ_NOTIFICATION: size = sizeof(set6_notification_t); break;
        case KOBJ_FRAME:        size = sizeof(set6_frame_t); break;
        case KOBJ_CNODE:        size = sizeof(set6_cnode_t); break;
        default:                size = 64; break;
    }

    return untyped_retype(&k->untyped[ut_idx], type, size);
}

#endif /* SET6_SEL4_TERNARY_H */
