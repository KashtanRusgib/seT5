/*
 * test_scheduler_concurrency.c - Scheduler concurrency and race condition tests
 *
 * Tests: Thread scheduling, priority handling, blocking/unblocking
 * Uses the actual seT6 scheduler API (sched_init, sched_create, etc.)
 */

#include <stdio.h>
#include "set6/scheduler.h"
#include "set6/trit.h"

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

/* ==== Scheduler Tests ================================================== */

void test_scheduler_thread_creation(void) {
    printf("Testing scheduler thread creation...\n");

    sched_state_t_state sched;
    sched_init(&sched);

    /* Create threads with different priorities */
    int t1 = sched_create(&sched, 0, TRIT_TRUE);
    CHECK("Create high-priority thread", t1 >= 0);

    int t2 = sched_create(&sched, 100, TRIT_UNKNOWN);
    CHECK("Create normal-priority thread", t2 >= 0);

    int t3 = sched_create(&sched, 200, TRIT_FALSE);
    CHECK("Create low-priority thread", t3 >= 0);

    /* Set priorities */
    CHECK("Set priority succeeds", sched_set_priority(&sched, t1, TRIT_TRUE) == 0);
    CHECK("Set priority succeeds", sched_set_priority(&sched, t2, TRIT_FALSE) == 0);

    /* Clean up */
    sched_destroy(&sched, t1);
    sched_destroy(&sched, t2);
    sched_destroy(&sched, t3);
}

void test_scheduler_priority_scheduling(void) {
    printf("Testing priority-based scheduling...\n");

    sched_state_t_state sched;
    sched_init(&sched);

    int high  = sched_create(&sched, 0, TRIT_TRUE);
    int norm  = sched_create(&sched, 100, TRIT_UNKNOWN);
    int low   = sched_create(&sched, 200, TRIT_FALSE);

    /* Pick next should prefer highest priority */
    int next = sched_pick_next(&sched);
    CHECK("Picks high-priority first", next == high);

    sched_destroy(&sched, high);
    sched_destroy(&sched, norm);
    sched_destroy(&sched, low);
}

void test_scheduler_yield(void) {
    printf("Testing scheduler yield...\n");

    sched_state_t_state sched;
    sched_init(&sched);

    int t1 = sched_create(&sched, 0, TRIT_UNKNOWN);
    int t2 = sched_create(&sched, 100, TRIT_UNKNOWN);

    /* Yield should return one of the created threads */
    int next = sched_yield(&sched);
    CHECK("Yield returns valid tid", next == t1 || next == t2);

    /* Multiple yields should always return a valid thread */
    for (int i = 0; i < 10; i++) {
        next = sched_yield(&sched);
        CHECK("Repeated yield stable", next == t1 || next == t2);
    }

    sched_destroy(&sched, t1);
    sched_destroy(&sched, t2);
}

void test_scheduler_block_unblock(void) {
    printf("Testing scheduler block/unblock...\n");

    sched_state_t_state sched;
    sched_init(&sched);

    int t1 = sched_create(&sched, 0, TRIT_UNKNOWN);
    int t2 = sched_create(&sched, 100, TRIT_UNKNOWN);

    /* Block t1 */
    CHECK("Block thread", sched_block(&sched, t1, 0) == 0);

    /* pick_next must skip blocked t1 and return t2 */
    int next = sched_pick_next(&sched);
    CHECK("pick_next skips blocked thread", next == t2);

    /* Unblock */
    CHECK("Unblock thread", sched_unblock(&sched, t1) == 0);

    /* Double unblock should fail (already ready) */
    int r = sched_unblock(&sched, t1);
    CHECK("Double unblock returns error", r == -1);

    sched_destroy(&sched, t1);
    sched_destroy(&sched, t2);
}

void test_scheduler_stats(void) {
    printf("Testing scheduler statistics...\n");

    sched_state_t_state sched;
    sched_init(&sched);

    int total, ready, blocked, ctx;
    sched_stats(&sched, &total, &ready, &blocked, &ctx);
    CHECK("Initial: 0 threads", total == 0);

    int t1 = sched_create(&sched, 0, TRIT_UNKNOWN);
    int t2 = sched_create(&sched, 100, TRIT_UNKNOWN);

    sched_stats(&sched, &total, &ready, &blocked, &ctx);
    CHECK("After create: 2 threads", total == 2);
    CHECK("After create: 2 ready", ready == 2);

    sched_block(&sched, t1, 0);
    sched_stats(&sched, &total, &ready, &blocked, &ctx);
    CHECK("After block: 1 blocked", blocked == 1);

    sched_destroy(&sched, t1);
    sched_destroy(&sched, t2);
}

void test_scheduler_capacity(void) {
    printf("Testing scheduler capacity...\n");

    sched_state_t_state sched;
    sched_init(&sched);

    /* Create many threads up to capacity */
    int tids[SCHED_MAX_THREADS];
    int count = 0;
    for (int i = 0; i < SCHED_MAX_THREADS; i++) {
        tids[i] = sched_create(&sched, i * 10, TRIT_UNKNOWN);
        if (tids[i] >= 0) count++;
        else break;
    }
    CHECK("Created max threads", count == SCHED_MAX_THREADS);

    /* Next create should fail */
    int overflow = sched_create(&sched, 0, TRIT_UNKNOWN);
    CHECK("Overflow create returns -1", overflow == -1);

    /* Clean up */
    for (int i = 0; i < count; i++) {
        sched_destroy(&sched, tids[i]);
    }
}

int main(void) {
    printf("=== seT6 Scheduler Concurrency Tests ===\n\n");

    test_scheduler_thread_creation();
    test_scheduler_priority_scheduling();
    test_scheduler_yield();
    test_scheduler_block_unblock();
    test_scheduler_stats();
    test_scheduler_capacity();

    printf("\n=== Results: %d/%d passed", tests_passed, tests_run);
    if (tests_failed > 0) {
        printf(" (%d FAILED)", tests_failed);
    }
    printf(" ===\n");

    return tests_failed > 0 ? 1 : 0;
}
