/**
 * @file test_time.c
 * @brief seT6 — Time Synchronization Protocol Test Suite
 *
 * Tests the Arch Linux–inspired time sync daemon:
 *   - Source management and quality levels
 *   - Time sync with best source selection
 *   - Skew detection and history tracking
 *   - MRAM persistent timestamps
 *   - Priority event queue dispatch
 *   - Replay attack detection
 *   - Clock advancement and status
 *
 * Target: 30+ assertions.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set5/trit.h"
#include "set5/trit_timesyncd.h"

/* ======================================================================== */
/*  Test Harness                                                            */
/* ======================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    tests_total++; \
    printf("  %-60s", name); \
} while(0)

#define PASS() do { \
    tests_passed++; \
    printf("[PASS]\n"); \
} while(0)

#define FAIL(msg) do { \
    tests_failed++; \
    printf("[FAIL] %s\n", msg); \
} while(0)

#define ASSERT(cond, msg) do { \
    if (cond) { PASS(); } else { FAIL(msg); } \
} while(0)

#define SECTION(name) printf("\n  --- %s ---\n", name)

/* ======================================================================== */
/*  Test: Initialization                                                    */
/* ======================================================================== */

static void test_init(void) {
    SECTION("Time Daemon Initialization");

    ttime_state_t ts;

    TEST("Init returns OK");
    ASSERT(ttime_init(&ts) == TTIME_OK, "init failed");

    TEST("Sync status is UNKNOWN (not yet synced)");
    ASSERT(ttime_get_status(&ts) == TRIT_UNKNOWN, "expected UNKNOWN");

    TEST("Source count starts at 0");
    ASSERT(ts.source_count == 0, "expected 0");

    TEST("MRAM record not valid");
    ASSERT(ts.mram_record.valid == 0, "expected not valid");

    TEST("Init with NULL");
    ASSERT(ttime_init(NULL) == TTIME_ERR_INIT, "expected ERR_INIT");
}

/* ======================================================================== */
/*  Test: Source Management                                                 */
/* ======================================================================== */

static void test_sources(void) {
    SECTION("Time Source Management");

    ttime_state_t ts;
    ttime_init(&ts);

    unsigned char auth[TTIME_AUTH_TOKEN_LEN] = {0x01, 0x02, 0x03, 0x04};

    TEST("Add stratum-1 source with auth");
    int id = ttime_add_source(&ts, "ntp.trit.local", 1, auth);
    ASSERT(id == 0, "expected source id 0");

    TEST("Source quality is HIGH");
    ASSERT(ts.sources[0].quality == TTIME_QUALITY_HIGH, "expected HIGH");

    TEST("Source is authenticated");
    ASSERT(ts.sources[0].authenticated == 1, "expected authenticated");

    TEST("Add stratum-3 source without auth");
    id = ttime_add_source(&ts, "pool.ntp.trit", 3, NULL);
    ASSERT(id == 1, "expected source id 1");

    TEST("Stratum-3 quality is MEDIUM");
    ASSERT(ts.sources[1].quality == TTIME_QUALITY_MEDIUM, "expected MEDIUM");

    TEST("Stratum-3 is not authenticated");
    ASSERT(ts.sources[1].authenticated == 0, "expected not auth");

    TEST("Source count is 2");
    ASSERT(ts.source_count == 2, "expected 2");
}

/* ======================================================================== */
/*  Test: Time Sync                                                         */
/* ======================================================================== */

static void test_sync(void) {
    SECTION("Time Synchronization");

    ttime_state_t ts;
    ttime_init(&ts);

    unsigned char auth[TTIME_AUTH_TOKEN_LEN] = {0xAA};

    /* Add sources */
    ttime_add_source(&ts, "stratum1", 1, auth);
    ttime_add_source(&ts, "stratum5", 5, NULL);

    /* Set an offset on source 0 */
    ts.sources[0].offset_us_x10 = 500;  /* 50us offset */
    ts.local_time_us_x10 = 10000;

    TEST("Sync selects best (stratum-1 auth)");
    ASSERT(ttime_sync(&ts) == TTIME_OK, "sync failed");

    TEST("Sync status is TRUE after sync");
    ASSERT(ttime_get_status(&ts) == TRIT_TRUE, "expected TRUE");

    TEST("Synced time incorporates offset");
    ASSERT(ts.synced_time_us_x10 == 10500, "expected 10500");

    TEST("Sync count incremented");
    ASSERT(ts.sync_count == 1, "expected 1");

    /* No sources — should fail */
    ttime_state_t ts2;
    ttime_init(&ts2);
    TEST("Sync with no sources — ERR_NOTFOUND");
    ASSERT(ttime_sync(&ts2) == TTIME_ERR_NOTFOUND, "expected ERR_NOTFOUND");
}

/* ======================================================================== */
/*  Test: Skew Detection                                                    */
/* ======================================================================== */

static void test_skew(void) {
    SECTION("Skew Detection & History");

    ttime_state_t ts;
    ttime_init(&ts);
    ts.local_time_us_x10 = 10000;
    ts.synced_time_us_x10 = 9990;  /* 1us skew x10 = 10 */

    TEST("Check skew — small, OK");
    long skew = ttime_check_skew(&ts);
    ASSERT(skew == 10, "expected 10");

    TEST("Record skew sample");
    ASSERT(ttime_record_skew(&ts, 10) == TTIME_OK, "record failed");

    TEST("Skew history count is 1");
    ASSERT(ts.skew.count == 1, "expected 1");

    TEST("Average skew is 10");
    ASSERT(ts.skew.avg_skew_us_x10 == 10, "expected 10");

    /* Large skew — should trigger error */
    ts.local_time_us_x10 = 200000;
    ts.synced_time_us_x10 = 0;

    TEST("Check large skew — ERR_SKEW");
    ASSERT(ttime_check_skew(&ts) == TTIME_ERR_SKEW, "expected ERR_SKEW");

    TEST("Sync status downgraded to FALSE");
    ASSERT(ttime_get_status(&ts) == TRIT_FALSE, "expected FALSE");
}

/* ======================================================================== */
/*  Test: MRAM Persistent Timestamps                                        */
/* ======================================================================== */

static void test_mram(void) {
    SECTION("MRAM Persistent Timestamps");

    ttime_state_t ts;
    ttime_init(&ts);

    TEST("Restore before store — ERR_NOTFOUND");
    ASSERT(ttime_mram_restore(&ts) == TTIME_ERR_NOTFOUND, "expected ERR_NOTFOUND");

    TEST("Store timestamp to MRAM");
    ASSERT(ttime_mram_store(&ts, 99999) == TTIME_OK, "store failed");

    TEST("MRAM record valid");
    ASSERT(ts.mram_record.valid == 1, "expected valid");

    TEST("Restore from MRAM");
    ASSERT(ttime_mram_restore(&ts) == 99999, "expected 99999");

    TEST("Sequence number incremented");
    ASSERT(ts.mram_record.sequence_number == 1, "expected 1");
}

/* ======================================================================== */
/*  Test: Event Priority Queue                                              */
/* ======================================================================== */

static void test_events(void) {
    SECTION("Priority Event Queue");

    ttime_state_t ts;
    ttime_init(&ts);

    TEST("Add high-priority event (deadline 1000)");
    int id = ttime_event_add(&ts, 1000, TTIME_PRIO_HIGH);
    ASSERT(id == 0, "expected event id 0");

    TEST("Add low-priority event (deadline 500)");
    id = ttime_event_add(&ts, 500, TTIME_PRIO_LOW);
    ASSERT(id == 1, "expected event id 1");

    TEST("Add medium-priority event (deadline 800)");
    id = ttime_event_add(&ts, 800, TTIME_PRIO_MEDIUM);
    ASSERT(id == 2, "expected event id 2");

    TEST("Dispatch next — picks HIGH (+1) first");
    int dispatched = ttime_event_dispatch(&ts, 900);
    ASSERT(dispatched == 0, "expected event 0 (high priority)");

    TEST("Dispatch next — picks MEDIUM (0)");
    dispatched = ttime_event_dispatch(&ts, 900);
    ASSERT(dispatched == 2, "expected event 2 (medium priority)");

    TEST("Check missed deadlines at time 600");
    int missed = ttime_event_check_missed(&ts, 600);
    ASSERT(missed == 1, "expected 1 missed (event 1 deadline=500)");
}

/* ======================================================================== */
/*  Test: Replay Attack Detection                                           */
/* ======================================================================== */

static void test_replay(void) {
    SECTION("Replay Attack Detection");

    ttime_state_t ts;
    ttime_init(&ts);

    /* Store first timestamp */
    ttime_mram_store(&ts, 10000);  /* seq=1 */

    TEST("Valid new sequence (2) — OK");
    ASSERT(ttime_detect_replay(&ts, 2) == TTIME_OK, "expected OK");

    TEST("Replay old sequence (1) — ERR_REPLAY");
    ASSERT(ttime_detect_replay(&ts, 1) == TTIME_ERR_REPLAY, "expected REPLAY");

    TEST("Replay same sequence (1) — ERR_REPLAY");
    ASSERT(ttime_detect_replay(&ts, 0) == TTIME_ERR_REPLAY, "expected REPLAY");

    TEST("Replay attempts counter");
    ASSERT(ts.replay_attempts == 2, "expected 2 replay attempts");
}

/* ======================================================================== */
/*  Test: Clock Management                                                  */
/* ======================================================================== */

static void test_clock(void) {
    SECTION("Clock Management");

    ttime_state_t ts;
    ttime_init(&ts);

    TEST("Initial local time is 0");
    ASSERT(ts.local_time_us_x10 == 0, "expected 0");

    TEST("Advance clock by 5000");
    ASSERT(ttime_clock_advance(&ts, 5000) == TTIME_OK, "advance failed");

    TEST("Local time is now 5000");
    ASSERT(ts.local_time_us_x10 == 5000, "expected 5000");

    TEST("Advance by another 3000");
    ttime_clock_advance(&ts, 3000);
    ASSERT(ts.local_time_us_x10 == 8000, "expected 8000");
}

/* ======================================================================== */
/*  Main                                                                    */
/* ======================================================================== */

int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  seT6 Time Synchronization Protocol Test Suite              ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    test_init();
    test_sources();
    test_sync();
    test_skew();
    test_mram();
    test_events();
    test_replay();
    test_clock();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Time Sync Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
        printf("=== Results: %d passed, %d failed ===\n",
            tests_passed, tests_failed);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed > 0 ? 1 : 0;
}
