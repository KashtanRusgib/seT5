/**
 * @file test_sel4_ternary.c
 * @brief Test suite for the seT5 seL4 Ternary Kernel Object Model
 *
 * Exercises all 10 kernel object types plus MDB, capability system,
 * scheduling, IPC, and memory management.
 *
 * Build: gcc -Wall -Wextra -Iinclude -Itools/compiler/include \
 *        -o test_sel4_ternary tests/test_sel4_ternary.c \
 *        src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "set5/sel4_ternary.h"
#include "set5/posix.h"

/* ---- Test harness ----------------------------------------------------- */

static int tests_run    = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define CHECK(desc, expr) do { \
    tests_run++; \
    if (expr) { \
        tests_passed++; \
        printf("  [PASS] %s\n", desc); \
    } else { \
        tests_failed++; \
        printf("  [FAIL] %s\n", desc); \
    } \
} while(0)

int main(void) {
    printf("seT5 seL4 Ternary Kernel — Test Suite\n");
    printf("======================================\n\n");

    /* ==== Kernel Init ================================================== */
    printf("-- Kernel Init --\n");
    set5_kernel_t k;
    set5_kernel_init(&k);

    CHECK("kernel init: tick = 0", k.tick == 0);
    CHECK("kernel init: no threads", k.tcb_count == 0);
    CHECK("kernel init: no endpoints", k.ep_count == 0);
    CHECK("kernel init: cnodes valid", k.cnodes[0].validity == TRIT_TRUE);
    CHECK("kernel init: irq control valid", k.irq_control.validity == TRIT_TRUE);
    CHECK("kernel init: mdb empty", k.mdb.count == 0);

    /* ==== Capabilities ================================================= */
    printf("\n-- Capabilities --\n");

    set5_cap_t root_cap = cap_mk(KOBJ_CNODE, 0, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE);
    CHECK("cap: root is valid", root_cap.validity == TRIT_TRUE);
    CHECK("cap: root can read", cap_has_right(&root_cap, root_cap.can_read) == TRIT_TRUE);
    CHECK("cap: root can write", cap_has_right(&root_cap, root_cap.can_write) == TRIT_TRUE);

    /* Derive with reduced rights */
    set5_cap_t child_cap = cap_derive(&root_cap, TRIT_TRUE, TRIT_FALSE, TRIT_FALSE, 42);
    CHECK("cap: child read = T", child_cap.can_read == TRIT_TRUE);
    CHECK("cap: child write = F (reduced)", child_cap.can_write == TRIT_FALSE);
    CHECK("cap: child grant = F (reduced)", child_cap.can_grant == TRIT_FALSE);
    CHECK("cap: child badge = 42", child_cap.badge == 42);
    CHECK("cap: monotonicity (write)", child_cap.can_write <= root_cap.can_write);

    /* Unknown derivation */
    set5_cap_t pending_cap = cap_derive(&root_cap, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_FALSE, 99);
    CHECK("cap: pending read = U", pending_cap.can_read == TRIT_UNKNOWN);

    /* Revoke */
    cap_revoke(&child_cap);
    CHECK("cap: revoked validity = F", child_cap.validity == TRIT_FALSE);
    CHECK("cap: revoked read scrubbed to U", child_cap.can_read == TRIT_UNKNOWN);

    /* Null cap */
    set5_cap_t null_cap = cap_mk_null();
    CHECK("cap: null type = NONE", null_cap.type == KOBJ_NONE);
    CHECK("cap: null validity = F", null_cap.validity == TRIT_FALSE);

    /* ==== CNode ======================================================== */
    printf("\n-- CNode --\n");

    set5_cnode_t *cn = &k.cnodes[0];
    CHECK("cnode: valid", cn->validity == TRIT_TRUE);
    CHECK("cnode: slot_count = 0", cn->slot_count == 0);

    /* Insert caps */
    set5_cap_t cap1 = cap_mk(KOBJ_ENDPOINT, 0, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE);
    CHECK("cnode: insert slot 0 ok", cnode_insert(cn, 0, cap1) == 0);
    CHECK("cnode: insert slot 1 ok", cnode_insert(cn, 1, root_cap) == 0);
    CHECK("cnode: slot_count = 2", cn->slot_count == 2);

    /* Lookup */
    set5_cap_t *looked = cnode_lookup(cn, 0);
    CHECK("cnode: lookup slot 0 type = ENDPOINT", looked && looked->type == KOBJ_ENDPOINT);
    CHECK("cnode: lookup slot 255 is null", cnode_lookup(cn, 255)->type == KOBJ_NONE);

    /* Double insert fails */
    CHECK("cnode: double insert fails", cnode_insert(cn, 0, cap1) == -2);

    /* Delete */
    CHECK("cnode: delete slot 0 ok", cnode_delete(cn, 0) == 0);
    CHECK("cnode: deleted slot is null", cnode_lookup(cn, 0)->type == KOBJ_NONE);

    /* Range check */
    CHECK("cnode: OOB lookup returns NULL", cnode_lookup(cn, -1) == NULL);
    CHECK("cnode: OOB lookup returns NULL (256)", cnode_lookup(cn, 256) == NULL);

    /* ==== TCB ========================================================== */
    printf("\n-- TCB --\n");

    int t0 = set5_create_thread(&k, TRIT_TRUE, TRIT_TRUE);
    int t1 = set5_create_thread(&k, TRIT_UNKNOWN, TRIT_UNKNOWN);
    int t2 = set5_create_thread(&k, TRIT_FALSE, TRIT_FALSE);

    CHECK("tcb: 3 threads created", k.tcb_count == 3);
    CHECK("tcb: t0 is running", k.tcbs[t0].state == THREAD_RUNNING);
    CHECK("tcb: t0 priority = T", k.tcbs[t0].priority == TRIT_TRUE);
    CHECK("tcb: t1 priority = U", k.tcbs[t1].priority == TRIT_UNKNOWN);
    CHECK("tcb: t2 domain = F", k.tcbs[t2].domain == TRIT_FALSE);

    /* Configure */
    tcb_configure(&k.tcbs[t0], 0, 0, -1, -1);
    CHECK("tcb: t0 cspace_root = 0", k.tcbs[t0].cspace_root == 0);

    /* Suspend and resume */
    tcb_suspend(&k.tcbs[t1]);
    CHECK("tcb: t1 suspended (blocked)", k.tcbs[t1].state == THREAD_BLOCKED);
    tcb_resume(&k.tcbs[t1]);
    CHECK("tcb: t1 resumed (running)", k.tcbs[t1].state == THREAD_RUNNING);

    /* Destroy */
    tcb_destroy(&k.tcbs[t2]);
    CHECK("tcb: t2 destroyed (inactive)", k.tcbs[t2].state == THREAD_INACTIVE);
    CHECK("tcb: t2 validity = F", k.tcbs[t2].validity == TRIT_FALSE);

    /* Register state */
    CHECK("tcb: t0 regs[0] = Unknown splat",
          trit2_reg32_get(&k.tcbs[t0].regs[0], 0) == TRIT2_UNKNOWN);

    /* ==== Scheduling =================================================== */
    printf("\n-- Scheduling --\n");

    int sched_result = set5_schedule(&k);
    CHECK("sched: picks a thread", sched_result >= 0);
    CHECK("sched: picks T-domain first", k.tcbs[sched_result].domain == TRIT_TRUE);
    CHECK("sched: current_domain = T", k.current_domain == TRIT_TRUE);
    CHECK("sched: tick incremented", k.tick > 0);

    /* After suspending T-domain thread, should pick U-domain */
    tcb_suspend(&k.tcbs[t0]);
    sched_result = set5_schedule(&k);
    CHECK("sched: picks U-domain after T suspended",
          k.tcbs[sched_result].domain == TRIT_UNKNOWN);

    tcb_resume(&k.tcbs[t0]); /* Restore */

    /* ==== Endpoints ==================================================== */
    printf("\n-- Endpoints --\n");

    int ep = set5_create_endpoint(&k);
    CHECK("ep: created", ep >= 0);
    CHECK("ep: valid", k.endpoints[ep].validity == TRIT_TRUE);
    CHECK("ep: idle state", k.endpoints[ep].queue_state == EP_IDLE);

    /* Enqueue sender */
    CHECK("ep: send enqueue ok", endpoint_send_enqueue(&k.endpoints[ep], t0) == TRIT_TRUE);
    CHECK("ep: state = SEND_BLOCKED", k.endpoints[ep].queue_state == EP_SEND_BLOCKED);

    /* Dequeue sender */
    int dequeued = endpoint_send_dequeue(&k.endpoints[ep]);
    CHECK("ep: dequeue = t0", dequeued == t0);
    CHECK("ep: back to idle", k.endpoints[ep].queue_state == EP_IDLE);

    /* Message transfer */
    set5_ipc_msg_t msg = {{TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE}, 42, t0};
    CHECK("ep: transfer ok", endpoint_transfer(&k.endpoints[ep], &msg) == TRIT_TRUE);
    CHECK("ep: msg badge preserved", k.endpoints[ep].last_msg.badge == 42);
    CHECK("ep: msg[0] = T", k.endpoints[ep].last_msg.msg[0] == TRIT_TRUE);

    /* IPC send via kernel */
    CHECK("ipc: kernel send ok", set5_ipc_send(&k, ep, &msg) == TRIT_TRUE);

    /* ==== Notifications ================================================ */
    printf("\n-- Notifications --\n");

    int ntf = set5_create_notification(&k);
    CHECK("ntf: created", ntf >= 0);
    CHECK("ntf: valid", k.notifications[ntf].validity == TRIT_TRUE);
    CHECK("ntf: poll = 0 (no signals)", notification_poll(&k.notifications[ntf]) == 0);

    /* Signal */
    CHECK("ntf: signal bit 5", notification_signal(&k.notifications[ntf], 5) == TRIT_TRUE);
    CHECK("ntf: signal bit 10", notification_signal(&k.notifications[ntf], 10) == TRIT_TRUE);
    CHECK("ntf: poll = 2", notification_poll(&k.notifications[ntf]) == 2);

    /* Wait (consume) */
    int consumed = notification_wait(&k.notifications[ntf]);
    CHECK("ntf: consumed 2 signals", consumed == 2);
    CHECK("ntf: poll after consume = 0", notification_poll(&k.notifications[ntf]) == 0);

    /* ==== Untyped Memory =============================================== */
    printf("\n-- Untyped Memory --\n");

    k.ut_count = 1;
    set5_untyped_t *ut = &k.untyped[0];
    CHECK("ut: initial watermark = 0", ut->watermark == 0);

    /* Retype into TCB */
    int child_idx = set5_untyped_retype(&k, 0, KOBJ_TCB);
    CHECK("ut: retype TCB ok", child_idx >= 0);
    CHECK("ut: children_count = 1", ut->children_count == 1);
    CHECK("ut: child type = TCB", ut->children[0] == KOBJ_TCB);

    /* Retype into endpoint */
    child_idx = set5_untyped_retype(&k, 0, KOBJ_ENDPOINT);
    CHECK("ut: retype EP ok", child_idx >= 0);
    CHECK("ut: children_count = 2", ut->children_count == 2);

    /* Revoke reclaims all */
    untyped_revoke(ut);
    CHECK("ut: revoke resets watermark", ut->watermark == 0);
    CHECK("ut: revoke resets children", ut->children_count == 0);
    CHECK("ut: revoke sets validity = U", ut->validity == TRIT_UNKNOWN);

    /* ==== Frames ======================================================= */
    printf("\n-- Frames --\n");

    set5_frame_t *fr = &k.frames[0];
    CHECK("frame: valid", fr->validity == TRIT_TRUE);
    CHECK("frame: unmapped", fr->mapped_vaddr == -1);

    /* Map */
    CHECK("frame: map ok", frame_map(fr, 0x1000, 0) == TRIT_TRUE);
    CHECK("frame: mapped_vaddr = 0x1000", fr->mapped_vaddr == 0x1000);
    CHECK("frame: mapped_asid = 0", fr->mapped_asid == 0);

    /* Double map returns U */
    CHECK("frame: double map = U", frame_map(fr, 0x2000, 0) == TRIT_UNKNOWN);

    /* Unmap */
    CHECK("frame: unmap ok", frame_unmap(fr) == TRIT_TRUE);
    CHECK("frame: unmapped after unmap", fr->mapped_vaddr == -1);

    /* ==== Page Tables ================================================== */
    printf("\n-- Page Tables --\n");

    set5_page_table_t *pt = &k.page_tables[0];
    CHECK("pt: valid", pt->validity == TRIT_TRUE);
    CHECK("pt: no mappings", pt->mapped_count == 0);

    /* Map a frame */
    CHECK("pt: map entry 0",
          page_table_map(pt, 0, 0, TRIT_TRUE, TRIT_FALSE, 0) == TRIT_TRUE);
    CHECK("pt: mapped_count = 1", pt->mapped_count == 1);

    /* Lookup */
    CHECK("pt: lookup 0 = frame 0", page_table_lookup(pt, 0) == 0);
    CHECK("pt: lookup 1 = -1 (unmapped)", page_table_lookup(pt, 1) == -1);

    /* Double map returns U */
    CHECK("pt: double map = U",
          page_table_map(pt, 0, 1, TRIT_TRUE, TRIT_FALSE, 0) == TRIT_UNKNOWN);

    /* PTE attributes */
    CHECK("pt: entry 0 writable = T", pt->entries[0].writable == TRIT_TRUE);
    CHECK("pt: entry 0 executable = F", pt->entries[0].executable == TRIT_FALSE);
    CHECK("pt: entry 0 user_access = T", pt->entries[0].user_access == TRIT_TRUE);

    /* Unmap */
    CHECK("pt: unmap entry 0", page_table_unmap(pt, 0) == TRIT_TRUE);
    CHECK("pt: mapped_count = 0", pt->mapped_count == 0);
    CHECK("pt: lookup 0 = -1 after unmap", page_table_lookup(pt, 0) == -1);

    /* ==== IRQ Control ================================================== */
    printf("\n-- IRQ Control --\n");

    CHECK("irq: control valid", k.irq_control.validity == TRIT_TRUE);

    /* Register handler */
    CHECK("irq: set handler 0", irq_handler_set(&k.irq_control, 0, ntf, t0) == TRIT_TRUE);
    CHECK("irq: handler 0 valid", k.irq_control.handlers[0].validity == TRIT_TRUE);
    CHECK("irq: handler 0 bound to ntf", k.irq_control.handlers[0].notif_index == ntf);

    /* Acknowledge */
    CHECK("irq: ack 0", irq_handler_ack(&k.irq_control, 0) == TRIT_TRUE);
    CHECK("irq: trigger_count = 1", k.irq_control.handlers[0].trigger_count == 1);

    /* Invalid IRQ */
    CHECK("irq: set handler OOB", irq_handler_set(&k.irq_control, 99, 0, 0) == TRIT_FALSE);

    /* ==== ASID Pools =================================================== */
    printf("\n-- ASID Pools --\n");

    set5_asid_pool_t *pool = &k.asid_pools[0];
    CHECK("asid: pool valid", pool->validity == TRIT_TRUE);
    CHECK("asid: initially empty", pool->allocated_count == 0);

    /* Allocate ASIDs */
    int asid0 = asid_pool_alloc(pool);
    int asid1 = asid_pool_alloc(pool);
    CHECK("asid: alloc 0", asid0 == 0);
    CHECK("asid: alloc 1", asid1 == 1);
    CHECK("asid: count = 2", pool->allocated_count == 2);
    CHECK("asid: slot 0 = T", pool->asids[0] == TRIT_TRUE);

    /* Free */
    CHECK("asid: free 0 ok", asid_pool_free(pool, 0) == TRIT_TRUE);
    CHECK("asid: count = 1", pool->allocated_count == 1);
    CHECK("asid: slot 0 = F after free", pool->asids[0] == TRIT_FALSE);

    /* ==== MDB (Mapping Database) ======================================= */
    printf("\n-- MDB --\n");

    int mdb_root = mdb_insert(&k.mdb, 0, 0, -1);
    CHECK("mdb: root inserted", mdb_root == 0);
    CHECK("mdb: root valid", k.mdb.entries[0].validity == TRIT_TRUE);

    int mdb_c1 = mdb_insert(&k.mdb, 0, 1, mdb_root);
    int mdb_c2 = mdb_insert(&k.mdb, 0, 2, mdb_root);
    CHECK("mdb: child1 inserted", mdb_c1 == 1);
    CHECK("mdb: child2 inserted", mdb_c2 == 2);
    CHECK("mdb: root has child", k.mdb.entries[mdb_root].first_child == mdb_c1);
    CHECK("mdb: child1 sibling = child2", k.mdb.entries[mdb_c1].next_sibling == mdb_c2);

    /* Grandchild */
    int mdb_gc = mdb_insert(&k.mdb, 0, 3, mdb_c1);
    CHECK("mdb: grandchild inserted", mdb_gc == 3);
    CHECK("mdb: child1 has grandchild", k.mdb.entries[mdb_c1].first_child == mdb_gc);

    /* Recursive revoke of child1 should revoke grandchild */
    mdb_revoke(&k.mdb, mdb_c1);
    CHECK("mdb: child1 revoked", k.mdb.entries[mdb_c1].validity == TRIT_FALSE);
    CHECK("mdb: grandchild revoked", k.mdb.entries[mdb_gc].validity == TRIT_FALSE);
    CHECK("mdb: child2 still valid", k.mdb.entries[mdb_c2].validity == TRIT_TRUE);

    /* ==== POSIX Translation ============================================ */
    printf("\n-- POSIX Translation --\n");

    CHECK("posix: errno(0) = T", posix_errno_to_trit(0) == TRIT_TRUE);
    CHECK("posix: errno(-11) = U (EAGAIN)", posix_errno_to_trit(-11) == TRIT_UNKNOWN);
    CHECK("posix: errno(-1) = F", posix_errno_to_trit(-1) == TRIT_FALSE);
    CHECK("posix: trit_to_errno(T) = 0", trit_to_posix_errno(TRIT_TRUE) == 0);
    CHECK("posix: trit_to_errno(U) = -11", trit_to_posix_errno(TRIT_UNKNOWN) == -11);

    CHECK("posix: nice(-10) = T", posix_nice_to_trit_priority(-10) == TRIT_TRUE);
    CHECK("posix: nice(0) = U", posix_nice_to_trit_priority(0) == TRIT_UNKNOWN);
    CHECK("posix: nice(10) = F", posix_nice_to_trit_priority(10) == TRIT_FALSE);

    /* FD table */
    posix_fd_table_t fdt;
    posix_fd_table_init(&fdt);
    CHECK("posix: stdin valid", posix_fd_check(&fdt, 0) == TRIT_TRUE);
    CHECK("posix: fd 99 invalid", posix_fd_check(&fdt, 99) == TRIT_FALSE);

    int fd = posix_fd_open(&fdt);
    CHECK("posix: open fd = 3", fd == 3);
    CHECK("posix: close fd 3", posix_fd_close(&fdt, 3) == 0);
    CHECK("posix: closed fd invalid", posix_fd_check(&fdt, 3) == TRIT_FALSE);

    /* ==== CNode Revoke All ============================================= */
    printf("\n-- CNode Revoke All --\n");

    set5_cnode_t cn2;
    cnode_init(&cn2);
    cnode_insert(&cn2, 0, cap_mk(KOBJ_TCB, 0, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE));
    cnode_insert(&cn2, 1, cap_mk(KOBJ_ENDPOINT, 0, TRIT_TRUE, TRIT_FALSE, TRIT_FALSE));
    CHECK("cnode2: 2 caps inserted", cn2.slot_count == 2);

    cnode_revoke_all(&cn2);
    CHECK("cnode2: validity = F after revoke", cn2.validity == TRIT_FALSE);
    CHECK("cnode2: slot[0] revoked", cn2.slots[0].validity == TRIT_FALSE);
    CHECK("cnode2: slot[1] revoked", cn2.slots[1].validity == TRIT_FALSE);

    /* Operations on revoked CNode fail */
    CHECK("cnode2: lookup on revoked = NULL", cnode_lookup(&cn2, 0) == NULL);
    CHECK("cnode2: insert on revoked = -1",
          cnode_insert(&cn2, 5, cap_mk(KOBJ_FRAME, 0, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE)) == -1);

    /* ==== Summary ====================================================== */
    printf("\n========================================\n");
    printf("seL4 Ternary: %d tests, %d passed, %d failed\n",
           tests_run, tests_passed, tests_failed);
    printf("========================================\n");

    if (tests_failed == 0) {
        printf("seL4 Ternary: ALL TESTS PASSED. Moonshot validated.\n");
    } else {
        printf("seL4 Ternary: %d FAILURES.\n", tests_failed);
    }

    return tests_failed ? 1 : 0;
}
