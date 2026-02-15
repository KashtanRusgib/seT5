/**
 * @file test_integration.c
 * @brief seT6 Full Integration Test — Boot → Alloc → IPC → Shutdown
 *
 * End-to-end scenario test exercising the full kernel lifecycle:
 *
 *   1. Boot: initialise all subsystems
 *   2. Thread creation: spawn producer and consumer threads
 *   3. Memory allocation: allocate shared page for IPC data
 *   4. Capability setup: create caps for the shared page
 *   5. IPC: producer sends data via endpoint, consumer receives
 *   6. Scheduling: yield between threads
 *   7. Multi-radix: DOT_TRIT on data, RADIX_CONV for encoding
 *   8. Teardown: revoke caps, free pages, destroy threads
 *   9. Shutdown: verify clean state
 *
 * Build: gcc -Wall -Wextra -Iinclude -Itools/compiler/include \
 *        -o test_integration tests/test_integration.c \
 *        src/memory.c src/ipc.c src/scheduler.c src/syscall.c src/multiradix.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "set6/trit.h"
#include "set6/trit_type.h"
#include "set6/trit_emu.h"
#include "set6/trit_cast.h"
#include "set6/syscall.h"
#include "set6/multiradix.h"

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

/* ==== Scenario: Producer-Consumer with Shared Memory =================== */

static void test_producer_consumer(void) {
    printf("\n=== Scenario: Producer-Consumer ===\n");

    kernel_state_t ks;
    kernel_init(&ks, 16);

    /* 1. Create producer and consumer threads */
    printf("\n--- Phase 1: Thread Creation ---\n");
    int producer = sched_create(&ks.sched, 0x1000, TRIT_TRUE);   /* high prio */
    int consumer = sched_create(&ks.sched, 0x2000, TRIT_UNKNOWN);/* normal */
    CHECK("producer thread created", producer >= 0);
    CHECK("consumer thread created", consumer >= 0);

    /* Set current thread to producer */
    ks.sched.current_tid = producer;

    /* 2. Allocate shared page */
    printf("\n--- Phase 2: Memory Allocation ---\n");
    int shared_page = mem_alloc(&ks.mem, producer);
    CHECK("shared page allocated", shared_page >= 0);

    /* Write data pattern to shared page */
    for (int i = 0; i < 8; i++) {
        trit data = (i % 3 == 0) ? TRIT_TRUE :
                    (i % 3 == 1) ? TRIT_UNKNOWN : TRIT_FALSE;
        int w = mem_write(&ks.mem, shared_page, i, data);
        CHECK("write to shared page succeeds", w == 0);
    }

    /* Verify data pattern */
    trit r0 = mem_read(&ks.mem, shared_page, 0);
    trit r1 = mem_read(&ks.mem, shared_page, 1);
    trit r2 = mem_read(&ks.mem, shared_page, 2);
    CHECK("shared page: slot 0 = True", r0 == TRIT_TRUE);
    CHECK("shared page: slot 1 = Unknown", r1 == TRIT_UNKNOWN);
    CHECK("shared page: slot 2 = False", r2 == TRIT_FALSE);

    /* 3. Create capabilities for shared page */
    printf("\n--- Phase 3: Capability Setup ---\n");
    int root_cap = kernel_cap_create(&ks, shared_page, 7, 0);  /* R|W|G */
    CHECK("root cap created", root_cap >= 0);

    /* Grant read-only cap to consumer */
    int consumer_cap = kernel_cap_grant(&ks, root_cap, 1);  /* READ only */
    CHECK("consumer cap granted", consumer_cap >= 0);
    CHECK("consumer can read", kernel_cap_check(&ks, consumer_cap, 1));
    CHECK("consumer cannot write", !kernel_cap_check(&ks, consumer_cap, 2));

    /* 4. IPC: producer sends data to consumer */
    printf("\n--- Phase 4: IPC Communication ---\n");
    int ep = ipc_endpoint_create(&ks.ipc);
    CHECK("endpoint created", ep >= 0);

    /* Producer sends message with data from shared page */
    ipc_msg_t msg;
    trit ipc_data[4] = {
        mem_read(&ks.mem, shared_page, 0),
        mem_read(&ks.mem, shared_page, 1),
        mem_read(&ks.mem, shared_page, 2),
        mem_read(&ks.mem, shared_page, 3)
    };
    ipc_msg_build(&msg, ipc_data, 4, 100, producer);
    int send_r = ipc_send(&ks.ipc, ep, &msg, producer);
    CHECK("producer send (blocks)", send_r == 1);

    /* Context switch to consumer */
    ks.sched.current_tid = consumer;
    ks.sched.context_switches++;

    /* Consumer receives */
    ipc_msg_t recv_msg;
    int recv_r = ipc_recv(&ks.ipc, ep, &recv_msg, consumer);
    CHECK("consumer recv success", recv_r == 0);
    CHECK("recv badge = 100", recv_msg.sender_badge == 100);
    CHECK("recv msg[0] = True", recv_msg.words[0] == TRIT_TRUE);
    CHECK("recv msg[1] = Unknown", recv_msg.words[1] == TRIT_UNKNOWN);
    CHECK("recv msg[2] = False", recv_msg.words[2] == TRIT_FALSE);

    /* 5. Scheduling: yield back to producer */
    printf("\n--- Phase 5: Scheduling ---\n");
    int next = sched_yield(&ks.sched);
    CHECK("yield picks producer (high prio)", next == producer);

    /* 6. Multi-radix: DOT_TRIT on received data */
    printf("\n--- Phase 6: Multi-Radix Compute ---\n");

    multiradix_state_t mr_state;
    multiradix_init(&mr_state);

    /* Load received data into register 0 */
    for (int i = 0; i < 4; i++) {
        trit2_reg32_set(&mr_state.regs[0], i,
                        trit_to_trit2(recv_msg.words[i]));
    }

    /* Load weights into register 1 (all True for identity) */
    mr_state.regs[1] = trit2_reg32_splat(TRIT2_UNKNOWN);
    for (int i = 0; i < 4; i++) {
        trit2_reg32_set(&mr_state.regs[1], i, TRIT2_TRUE);
    }

    int dp = dot_trit(&mr_state, 0, 1);
    /* T*T + U*T + F*T + T*T = +1 + 0 + (-1) + 1 = +1 */
    CHECK("DOT_TRIT on received data = +1", dp == 1);

    /* RADIX_CONV: encode the dot product result */
    int nz = radix_conv_to_ternary(&mr_state, 2, dp);
    int back = radix_conv_to_binary(&mr_state, 2, 20);
    CHECK("RADIX_CONV roundtrip of dot result", back == dp);

    /* Telemetry */
    trit_lb_snapshot_t snap = trit_lb_snapshot(&mr_state);
    CHECK("telemetry: 2 trit instructions", snap.total_insns >= 2);

    /* 7. Teardown */
    printf("\n--- Phase 7: Teardown ---\n");

    /* Revoke consumer cap */
    int rev = kernel_cap_revoke(&ks, consumer_cap);
    CHECK("consumer cap revoked", rev == 0);
    CHECK("consumer cap no longer valid", !kernel_cap_check(&ks, consumer_cap, 1));

    /* Free shared page */
    int fr = mem_free(&ks.mem, shared_page);
    CHECK("shared page freed", fr == 0);

    /* Verify scrub-on-free */
    trit scrubbed = mem_read(&ks.mem, shared_page, 0);
    CHECK("freed page scrubbed to Unknown", scrubbed == TRIT_UNKNOWN);

    /* Destroy threads */
    int dp1 = sched_destroy(&ks.sched, producer);
    int dc1 = sched_destroy(&ks.sched, consumer);
    CHECK("producer destroyed", dp1 == 0);
    CHECK("consumer destroyed", dc1 == 0);

    /* Destroy endpoint */
    int ed = ipc_endpoint_destroy(&ks.ipc, ep);
    CHECK("endpoint destroyed", ed == 0);

    /* 8. Verify clean state */
    printf("\n--- Phase 8: Clean State Verification ---\n");
    int total, free_pg, alloc;
    mem_stats(&ks.mem, &total, &free_pg, &alloc);
    CHECK("all pages freed after teardown", alloc == 0);

    int total_t, ready_t, blocked_t, ctx;
    sched_stats(&ks.sched, &total_t, &ready_t, &blocked_t, &ctx);
    CHECK("no ready threads after teardown", ready_t == 0);
    CHECK("no blocked threads after teardown", blocked_t == 0);
}

/* ==== Scenario: Notification-Driven Event Loop ========================= */

static void test_notification_event_loop(void) {
    printf("\n=== Scenario: Notification Event Loop ===\n");

    kernel_state_t ks;
    kernel_init(&ks, 8);

    /* Create an event handler thread */
    int handler = sched_create(&ks.sched, 0x3000, TRIT_TRUE);
    ks.sched.current_tid = handler;
    CHECK("handler thread created", handler >= 0);

    /* Create notification object */
    int notif = ipc_notification_create(&ks.ipc);
    CHECK("notification created", notif >= 0);

    /* Simulate event loop: wait → signal → process → repeat 3 times */
    for (int cycle = 0; cycle < 3; cycle++) {
        /* Signal the notification (simulating an interrupt/event) */
        int sig = ipc_signal(&ks.ipc, notif);
        CHECK("signal succeeds", sig == 0);

        /* Wait (should be immediate since we just signaled) */
        int wait = ipc_wait(&ks.ipc, notif, handler);
        CHECK("wait immediate after signal", wait == 0);
    }

    /* Final wait with no pending signal → blocks */
    int wait = ipc_wait(&ks.ipc, notif, handler);
    CHECK("wait blocks (no pending signal)", wait == 1);

    /* Teardown */
    sched_destroy(&ks.sched, handler);

    int total_t, ready_t, blocked_t, ctx;
    sched_stats(&ks.sched, &total_t, &ready_t, &blocked_t, &ctx);
    CHECK("handler dead after destroy", ready_t == 0);
}

/* ==== Scenario: Full RADIX_CONV + DOT_TRIT Pipeline ==================== */

static void test_radix_dot_pipeline(void) {
    printf("\n=== Scenario: Radix→Dot Pipeline ===\n");

    multiradix_state_t mr;
    multiradix_init(&mr);

    /* Encode two integers into ternary registers */
    radix_conv_to_ternary(&mr, 0, 13);   /* reg 0 ← balanced(13)  */
    radix_conv_to_ternary(&mr, 1, -13);  /* reg 1 ← balanced(-13) */

    /* Verify roundtrip */
    int v0 = radix_conv_to_binary(&mr, 0, 20);
    int v1 = radix_conv_to_binary(&mr, 1, 20);
    CHECK("reg0 = 13", v0 == 13);
    CHECK("reg1 = -13", v1 == -13);

    /* DOT_TRIT of a number with its negation */
    int dp = dot_trit(&mr, 0, 1);
    /* 13 × (-13) in ternary: each trit pos has val × (-val) = -val² ≤ 0 */
    CHECK("dot(x, -x) <= 0", dp <= 0);

    /* DOT_TRIT of a number with itself (norm²) */
    int norm = dot_trit(&mr, 0, 0);
    CHECK("dot(x, x) > 0", norm > 0);

    /* FFT butterfly on the result register */
    radix_conv_to_ternary(&mr, 5, 42);
    int groups = fft_step(&mr, 5, 6, 1);
    CHECK("FFT on radix-converted data", groups > 0);

    /* Telemetry should reflect all operations */
    trit_lb_snapshot_t snap = trit_lb_snapshot(&mr);
    CHECK("pipeline: telemetry total > 0", snap.total_insns > 0);
    CHECK("pipeline: trit ratio >= 50%", snap.trit_ratio_pct >= 50);
}

/* ==== Entry Point ====================================================== */

int main(void) {
    printf("seT6 Integration Test Suite\n");
    printf("===========================\n");

    test_producer_consumer();
    test_notification_event_loop();
    test_radix_dot_pipeline();

    printf("\n========================================\n");
    printf("Integration: %d tests, %d passed, %d failed\n",
           tests_run, tests_passed, tests_failed);
    printf("========================================\n");

    if (tests_failed == 0) {
        printf("ALL INTEGRATION TESTS PASSED.\n");
    } else {
        printf("%d INTEGRATION FAILURES.\n", tests_failed);
    }

    return tests_failed;
}
