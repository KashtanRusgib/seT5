/**
 * @file test_adversarial.c
 * @brief Adversarial / negative-path test suite for seT5 kernel
 *
 * Validates robustness against boundary conditions, resource exhaustion,
 * invalid inputs, double-free, use-after-free, capability escalation,
 * and other adversarial scenarios across all core subsystems.
 */

#include "set5/trit.h"
#include "set5/memory.h"
#include "set5/ipc.h"
#include "set5/scheduler.h"
#include "set5/syscall.h"
#include <stdio.h>
#include <string.h>

/* ── Test infrastructure ── */

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) \
    do { printf("  %-55s ", #name); fflush(stdout); } while(0)

#define PASS() \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

#define FAIL(msg) \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

/* ════════════════════════════════════════════════════════════
 * Memory Adversarial Tests
 * ════════════════════════════════════════════════════════════ */

void test_mem_out_of_range_page(void) {
    TEST(mem_read_write_out_of_range_page);
    set5_mem_t mem;
    mem_init(&mem, 4);
    int p = mem_alloc(&mem, 0);

    /* Read/write with out-of-range page index */
    ASSERT_EQ(mem_read(&mem, -1, 0), TRIT_UNKNOWN, "read page -1");
    ASSERT_EQ(mem_read(&mem, 999, 0), TRIT_UNKNOWN, "read page 999");
    ASSERT_EQ(mem_write(&mem, -1, 0, TRIT_TRUE), -1, "write page -1");
    ASSERT_EQ(mem_write(&mem, 999, 0, TRIT_TRUE), -1, "write page 999");
    (void)p;
    PASS();
}

void test_mem_out_of_range_offset(void) {
    TEST(mem_read_write_out_of_range_offset);
    set5_mem_t mem;
    mem_init(&mem, 4);
    int p = mem_alloc(&mem, 0);

    ASSERT_EQ(mem_read(&mem, p, -1), TRIT_UNKNOWN, "read offset -1");
    ASSERT_EQ(mem_read(&mem, p, SET5_PAGE_TRITS), TRIT_UNKNOWN, "read offset max");
    ASSERT_EQ(mem_write(&mem, p, -1, TRIT_TRUE), -1, "write offset -1");
    ASSERT_EQ(mem_write(&mem, p, SET5_PAGE_TRITS, TRIT_TRUE), -1, "write offset max");
    PASS();
}

void test_mem_double_free(void) {
    TEST(mem_double_free_rejected);
    set5_mem_t mem;
    mem_init(&mem, 4);
    int p = mem_alloc(&mem, 0);

    ASSERT_EQ(mem_free(&mem, p), 0, "first free ok");
    ASSERT_EQ(mem_free(&mem, p), -1, "double free rejected");
    PASS();
}

void test_mem_use_after_free(void) {
    TEST(mem_use_after_free_returns_unknown);
    set5_mem_t mem;
    mem_init(&mem, 4);
    int p = mem_alloc(&mem, 0);

    mem_write(&mem, p, 0, TRIT_TRUE);
    mem_free(&mem, p);

    /* After free, read should return UNKNOWN (scrub-on-free) */
    ASSERT_EQ(mem_read(&mem, p, 0), TRIT_UNKNOWN, "use-after-free read");
    /* Write to freed page should fail */
    ASSERT_EQ(mem_write(&mem, p, 0, TRIT_TRUE), -1, "use-after-free write");
    PASS();
}

void test_mem_oom_exhaustion(void) {
    TEST(mem_oom_exhaustion);
    set5_mem_t mem;
    mem_init(&mem, 4);

    /* Allocate all pages */
    for (int i = 0; i < 4; i++) {
        ASSERT_TRUE(mem_alloc(&mem, 0) >= 0, "alloc before OOM");
    }
    /* Next allocation must fail */
    ASSERT_EQ(mem_alloc(&mem, 0), -1, "OOM returns -1");
    PASS();
}

void test_mem_write_readonly(void) {
    TEST(mem_write_to_readonly_page);
    set5_mem_t mem;
    mem_init(&mem, 4);
    int p = mem_alloc(&mem, 0);

    /* Set page read-only via direct flag manipulation */
    mem.pages[p].flags |= PAGE_FLAG_READONLY;

    ASSERT_EQ(mem_write(&mem, p, 0, TRIT_TRUE), -1, "write readonly rejected");
    /* Read should still work */
    ASSERT_EQ(mem_read(&mem, p, 0), TRIT_UNKNOWN, "read readonly ok");
    PASS();
}

void test_mem_reserve_allocated(void) {
    TEST(mem_reserve_already_allocated_page);
    set5_mem_t mem;
    mem_init(&mem, 4);
    int p = mem_alloc(&mem, 0);

    /* Reserving an already-allocated page should fail */
    ASSERT_EQ(mem_reserve(&mem, p), -1, "reserve allocated rejected");
    PASS();
}

void test_mem_free_reserved(void) {
    TEST(mem_free_reserved_page);
    set5_mem_t mem;
    mem_init(&mem, 4);

    /* Reserve page 0 (which starts as free/UNKNOWN) */
    ASSERT_EQ(mem_reserve(&mem, 0), 0, "reserve ok");
    /* Freeing a reserved page should fail (valid == FALSE, not TRUE) */
    ASSERT_EQ(mem_free(&mem, 0), -1, "free reserved rejected");
    PASS();
}

void test_mem_init_clamps(void) {
    TEST(mem_init_clamps_page_count);
    set5_mem_t mem;
    mem_init(&mem, 9999);
    int total, fr, al;
    mem_stats(&mem, &total, &fr, &al);
    ASSERT_TRUE(total <= SET5_MAX_PAGES, "clamped to max");

    mem_init(&mem, -5);
    mem_stats(&mem, &total, &fr, &al);
    ASSERT_TRUE(total >= 0, "clamped negative to 0");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * IPC Adversarial Tests
 * ════════════════════════════════════════════════════════════ */

void test_ipc_send_destroyed_endpoint(void) {
    TEST(ipc_send_on_destroyed_endpoint);
    ipc_state_t ipc;
    ipc_init(&ipc);
    int ep = ipc_endpoint_create(&ipc);

    ipc_endpoint_destroy(&ipc, ep);

    ipc_msg_t msg;
    memset(&msg, 0, sizeof(msg));
    ASSERT_EQ(ipc_send(&ipc, ep, &msg, 0), -1, "send destroyed rejected");
    PASS();
}

void test_ipc_recv_destroyed_endpoint(void) {
    TEST(ipc_recv_on_destroyed_endpoint);
    ipc_state_t ipc;
    ipc_init(&ipc);
    int ep = ipc_endpoint_create(&ipc);

    ipc_endpoint_destroy(&ipc, ep);

    ipc_msg_t msg;
    ASSERT_EQ(ipc_recv(&ipc, ep, &msg, 0), -1, "recv destroyed rejected");
    PASS();
}

void test_ipc_double_destroy(void) {
    TEST(ipc_double_destroy_endpoint);
    ipc_state_t ipc;
    ipc_init(&ipc);
    int ep = ipc_endpoint_create(&ipc);

    ASSERT_EQ(ipc_endpoint_destroy(&ipc, ep), 0, "first destroy ok");
    ASSERT_EQ(ipc_endpoint_destroy(&ipc, ep), -1, "double destroy rejected");
    PASS();
}

void test_ipc_endpoint_exhaustion(void) {
    TEST(ipc_endpoint_exhaustion);
    ipc_state_t ipc;
    ipc_init(&ipc);

    for (int i = 0; i < IPC_MAX_ENDPOINTS; i++) {
        ASSERT_TRUE(ipc_endpoint_create(&ipc) >= 0, "create before full");
    }
    ASSERT_EQ(ipc_endpoint_create(&ipc), -1, "exhaustion returns -1");
    PASS();
}

void test_ipc_out_of_range_ep(void) {
    TEST(ipc_send_recv_out_of_range);
    ipc_state_t ipc;
    ipc_init(&ipc);

    ipc_msg_t msg;
    memset(&msg, 0, sizeof(msg));

    ASSERT_EQ(ipc_send(&ipc, -1, &msg, 0), -1, "send ep -1");
    ASSERT_EQ(ipc_send(&ipc, 999, &msg, 0), -1, "send ep 999");
    ASSERT_EQ(ipc_recv(&ipc, -1, &msg, 0), -1, "recv ep -1");
    ASSERT_EQ(ipc_recv(&ipc, 999, &msg, 0), -1, "recv ep 999");
    PASS();
}

void test_ipc_msg_build_overflow(void) {
    TEST(ipc_msg_build_length_clamped);
    ipc_msg_t msg;
    trit words[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};

    /* Build with length > IPC_MSG_MAX_WORDS — should clamp */
    ipc_msg_build(&msg, words, 999, 42, 1);
    ASSERT_TRUE(msg.length <= IPC_MSG_MAX_WORDS, "length clamped");
    ASSERT_EQ(msg.sender_badge, 42, "badge preserved");
    PASS();
}

void test_ipc_notification_exhaustion(void) {
    TEST(ipc_notification_exhaustion);
    ipc_state_t ipc;
    ipc_init(&ipc);

    for (int i = 0; i < IPC_MAX_NOTIFICATIONS; i++) {
        ASSERT_TRUE(ipc_notification_create(&ipc) >= 0, "notif create ok");
    }
    ASSERT_EQ(ipc_notification_create(&ipc), -1, "notif exhaustion");
    PASS();
}

void test_ipc_signal_out_of_range(void) {
    TEST(ipc_signal_wait_out_of_range);
    ipc_state_t ipc;
    ipc_init(&ipc);

    ASSERT_EQ(ipc_signal(&ipc, -1), -1, "signal idx -1");
    ASSERT_EQ(ipc_signal(&ipc, 999), -1, "signal idx 999");
    ASSERT_EQ(ipc_wait(&ipc, -1, 0), -1, "wait idx -1");
    ASSERT_EQ(ipc_wait(&ipc, 999, 0), -1, "wait idx 999");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Capability / Syscall Adversarial Tests
 * ════════════════════════════════════════════════════════════ */

void test_cap_grant_without_grant_right(void) {
    TEST(cap_grant_without_GRANT_right);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    /* Create cap with R+W (3) but no GRANT (4) */
    int cap = kernel_cap_create(&ks, 100, 3, 0);
    ASSERT_TRUE(cap >= 0, "cap created");

    /* Grant should fail — no GRANT right */
    int derived = kernel_cap_grant(&ks, cap, 1);
    ASSERT_EQ(derived, -1, "grant without G right rejected");
    PASS();
}

void test_cap_grant_from_revoked(void) {
    TEST(cap_grant_from_revoked_cap);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    int cap = kernel_cap_create(&ks, 100, 7, 0);  /* R+W+G */
    kernel_cap_revoke(&ks, cap);

    int derived = kernel_cap_grant(&ks, cap, 1);
    ASSERT_EQ(derived, -1, "grant from revoked rejected");
    PASS();
}

void test_cap_rights_monotonicity(void) {
    TEST(cap_grant_rights_monotonically_narrow);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    /* Source cap: R+W+G (7) */
    int src = kernel_cap_create(&ks, 100, 7, 0);
    ASSERT_TRUE(src >= 0, "source created");

    /* Grant with R only (1) — should succeed with rights = 1 */
    int derived = kernel_cap_grant(&ks, src, 1);
    ASSERT_TRUE(derived >= 0, "grant succeeded");

    /* Derived cap should have R but not W or G */
    ASSERT_EQ(kernel_cap_check(&ks, derived, 1), 1, "has READ");
    ASSERT_EQ(kernel_cap_check(&ks, derived, 2), 0, "no WRITE");
    ASSERT_EQ(kernel_cap_check(&ks, derived, 4), 0, "no GRANT");
    PASS();
}

void test_cap_exhaustion(void) {
    TEST(cap_table_exhaustion);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    for (int i = 0; i < SYSCALL_MAX_CAPS; i++) {
        ASSERT_TRUE(kernel_cap_create(&ks, i, 1, 0) >= 0, "cap create ok");
    }
    ASSERT_EQ(kernel_cap_create(&ks, 999, 1, 0), -1, "cap exhaustion");
    PASS();
}

void test_cap_double_revoke(void) {
    TEST(cap_double_revoke);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    int cap = kernel_cap_create(&ks, 100, 7, 0);
    ASSERT_EQ(kernel_cap_revoke(&ks, cap), 0, "first revoke ok");
    /* Second revoke — may succeed or fail depending on impl */
    int r = kernel_cap_revoke(&ks, cap);
    ASSERT_TRUE(r == 0 || r == -1, "double revoke handled");
    PASS();
}

void test_cap_check_invalid_index(void) {
    TEST(cap_check_invalid_index_denied);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    /* Out-of-range indices should be denied (return 0) */
    ASSERT_EQ(kernel_cap_check(&ks, -1, 1), 0, "check idx -1 denied");
    ASSERT_EQ(kernel_cap_check(&ks, 999, 1), 0, "check idx 999 denied");
    PASS();
}

void test_syscall_invalid_number(void) {
    TEST(syscall_dispatch_invalid_sysno);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    syscall_result_t r = syscall_dispatch(&ks, -1, 0, 0);
    ASSERT_EQ(r.retval, -1, "sysno -1 returns -1");

    r = syscall_dispatch(&ks, 999, 0, 0);
    ASSERT_EQ(r.retval, -1, "sysno 999 returns -1");
    PASS();
}

void test_stack_overflow_underflow(void) {
    TEST(operand_stack_overflow_and_underflow);
    kernel_state_t ks;
    kernel_init(&ks, 4);

    /* Push beyond capacity (64) */
    for (int i = 0; i < 70; i++) {
        kernel_push(&ks, TRIT_TRUE);
    }
    /* Stack should be capped at 64, no crash */
    ASSERT_TRUE(ks.operand_sp <= 64, "stack capped");

    /* Drain stack */
    for (int i = 0; i < 70; i++) {
        kernel_pop(&ks);
    }
    /* Underflow returns UNKNOWN */
    trit v = kernel_pop(&ks);
    ASSERT_EQ(v, TRIT_UNKNOWN, "underflow returns UNKNOWN");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Scheduler Adversarial Tests
 * ════════════════════════════════════════════════════════════ */

void test_sched_thread_exhaustion(void) {
    TEST(sched_thread_exhaustion);
    sched_state_t_state sched;
    sched_init(&sched);

    for (int i = 0; i < SCHED_MAX_THREADS; i++) {
        ASSERT_TRUE(sched_create(&sched, 0x1000, TRIT_UNKNOWN) >= 0,
                     "thread create ok");
    }
    ASSERT_EQ(sched_create(&sched, 0x1000, TRIT_UNKNOWN), -1,
              "thread exhaustion");
    PASS();
}

void test_sched_double_destroy(void) {
    TEST(sched_double_destroy_thread);
    sched_state_t_state sched;
    sched_init(&sched);
    int tid = sched_create(&sched, 0x1000, TRIT_UNKNOWN);

    ASSERT_EQ(sched_destroy(&sched, tid), 0, "first destroy ok");
    ASSERT_EQ(sched_destroy(&sched, tid), -1, "double destroy rejected");
    PASS();
}

void test_sched_invalid_tid(void) {
    TEST(sched_ops_invalid_tid);
    sched_state_t_state sched;
    sched_init(&sched);

    ASSERT_EQ(sched_destroy(&sched, -1), -1, "destroy tid -1");
    ASSERT_EQ(sched_destroy(&sched, 999), -1, "destroy tid 999");
    ASSERT_EQ(sched_block(&sched, -1, 0), -1, "block tid -1");
    ASSERT_EQ(sched_block(&sched, 999, 0), -1, "block tid 999");
    ASSERT_EQ(sched_unblock(&sched, -1), -1, "unblock tid -1");
    ASSERT_EQ(sched_unblock(&sched, 999), -1, "unblock tid 999");
    PASS();
}

void test_sched_unblock_non_blocked(void) {
    TEST(sched_unblock_non_blocked_rejected);
    sched_state_t_state sched;
    sched_init(&sched);
    int tid = sched_create(&sched, 0x1000, TRIT_UNKNOWN);

    /* Thread is READY, not BLOCKED — unblock should fail */
    ASSERT_EQ(sched_unblock(&sched, tid), -1, "unblock ready rejected");
    PASS();
}

void test_sched_invalid_priority(void) {
    TEST(sched_set_invalid_priority);
    sched_state_t_state sched;
    sched_init(&sched);
    int tid = sched_create(&sched, 0x1000, TRIT_UNKNOWN);

    /* Out-of-range priorities should be rejected by set_priority */
    ASSERT_EQ(sched_set_priority(&sched, tid, (trit)2), -1, "priority 2 rejected");
    ASSERT_EQ(sched_set_priority(&sched, tid, (trit)-2), -1, "priority -2 rejected");
    PASS();
}

void test_sched_yield_empty(void) {
    TEST(sched_yield_no_threads);
    sched_state_t_state sched;
    sched_init(&sched);

    /* No threads → yield returns -1 */
    int next = sched_yield(&sched);
    ASSERT_EQ(next, -1, "yield empty returns -1");
    PASS();
}

void test_sched_pick_all_dead(void) {
    TEST(sched_pick_next_all_dead);
    sched_state_t_state sched;
    sched_init(&sched);

    int t1 = sched_create(&sched, 0x1000, TRIT_UNKNOWN);
    int t2 = sched_create(&sched, 0x2000, TRIT_UNKNOWN);
    sched_destroy(&sched, t1);
    sched_destroy(&sched, t2);

    ASSERT_EQ(sched_pick_next(&sched), -1, "no runnable threads");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Trit Type Adversarial Tests
 * ════════════════════════════════════════════════════════════ */

void test_trit_pack_unpack_roundtrip(void) {
    TEST(trit_pack_unpack_roundtrip);
    /* All three trit values roundtrip correctly after the trit_pack fix.
     * Encoding: FALSE(-1)→0b10, UNKNOWN(0)→0b00, TRUE(+1)→0b01. */
    trit_packed p0 = trit_pack(TRIT_UNKNOWN);
    ASSERT_EQ(trit_unpack(p0), TRIT_UNKNOWN, "UNKNOWN roundtrips");
    trit_packed p1 = trit_pack(TRIT_TRUE);
    ASSERT_EQ(trit_unpack(p1), TRIT_TRUE, "TRUE roundtrips");
    trit_packed pf = trit_pack(TRIT_FALSE);
    ASSERT_EQ(pf, 2, "FALSE packs to 0b10");
    ASSERT_EQ(trit_unpack(pf), TRIT_FALSE, "FALSE roundtrips");
    PASS();
}

void test_trit_fault_encoding(void) {
    TEST(trit_unpack_fault_code_returns_unknown);
    /* Packed value 0b11 is the fault code → should unpack to UNKNOWN */
    trit u = trit_unpack(3);
    ASSERT_EQ(u, TRIT_UNKNOWN, "fault code maps to UNKNOWN");
    PASS();
}

/* ── Main ── */

int main(void) {
    printf("=== Adversarial / Negative-Path Test Suite ===\n\n");

    printf("[Memory Adversarial]\n");
    test_mem_out_of_range_page();
    test_mem_out_of_range_offset();
    test_mem_double_free();
    test_mem_use_after_free();
    test_mem_oom_exhaustion();
    test_mem_write_readonly();
    test_mem_reserve_allocated();
    test_mem_free_reserved();
    test_mem_init_clamps();

    printf("\n[IPC Adversarial]\n");
    test_ipc_send_destroyed_endpoint();
    test_ipc_recv_destroyed_endpoint();
    test_ipc_double_destroy();
    test_ipc_endpoint_exhaustion();
    test_ipc_out_of_range_ep();
    test_ipc_msg_build_overflow();
    test_ipc_notification_exhaustion();
    test_ipc_signal_out_of_range();

    printf("\n[Capability / Syscall Adversarial]\n");
    test_cap_grant_without_grant_right();
    test_cap_grant_from_revoked();
    test_cap_rights_monotonicity();
    test_cap_exhaustion();
    test_cap_double_revoke();
    test_cap_check_invalid_index();
    test_syscall_invalid_number();
    test_stack_overflow_underflow();

    printf("\n[Scheduler Adversarial]\n");
    test_sched_thread_exhaustion();
    test_sched_double_destroy();
    test_sched_invalid_tid();
    test_sched_unblock_non_blocked();
    test_sched_invalid_priority();
    test_sched_yield_empty();
    test_sched_pick_all_dead();

    printf("\n[Trit Type Adversarial]\n");
    test_trit_pack_unpack_roundtrip();
    test_trit_fault_encoding();

    printf("\n=== Results: %d passed, %d failed ===\n", tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
