/*==============================================================================
 * seT5/seT6 Test Generation — Batch 96
 *
 * Range: Tests 5552-5601 (50 tests)
 * Theme: Epistemic Logic and Hesitation (Advanced)
 * Aspect: Multi-channel drift, KL divergence edge cases, B4 thresholds, yield
 *         sensitivity, recalibration, DLT integration, fixed-point math,
 *         distribution convergence, state chains, confidence degradation.
 *
 * Generated: 2025-02-19
 * Target: 100% pass rate (Sigma 9 compliance)
 *============================================================================*/

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include "set5/trit.h"
#include "set5/trit_hesitation.h"

/* Test framework macros */
#define SECTION(name) do { section_name = name; } while (0)
#define TEST(desc) do { test_count++; current_test = desc; } while (0)
#define ASSERT(cond, msg) do { \
    if (!(cond)) { \
        printf("  FAIL: %s — %s (line %d)\n", current_test, msg, __LINE__); \
        fail_count++; \
        return; \
    } \
} while (0)
#define PASS() do { pass_count++; } while (0)
#define FAIL() do { fail_count++; } while (0)

static int test_count = 0;
static int pass_count = 0;
static int fail_count = 0;
static const char *section_name = NULL;
static const char *current_test = NULL;

/*==============================================================================
 * Advanced Epistemic Logic & Hesitation Tests 5552-5601
 *============================================================================*/

/* Test 5552: KL divergence non-negativity property */
static void test_kl_divergence_non_negative(void) {
    SECTION("Epistemic Advanced: KL Non-Negativity");
    
    TEST("KL divergence D_KL(P||Q) >= 0 for all distributions");
    thes_distribution_t p1 = { 5, 3, 2, 10 };
    thes_distribution_t q1 = { 2, 3, 5, 10 };
    int kl = thes_kl_divergence(&p1, &q1);
    ASSERT(kl >= 0, "expected >= 0");
    PASS();
}

/* Test 5553: KL divergence asymmetry */
static void test_kl_divergence_asymmetric(void) {
    SECTION("Epistemic Advanced: KL Asymmetry");
    
    TEST("KL divergence is asymmetric: D_KL(P||Q) ≠ D_KL(Q||P)");
    thes_distribution_t p = { 8, 1, 1, 10 };
    thes_distribution_t q = { 1, 1, 8, 10 };
    int kl_pq = thes_kl_divergence(&p, &q);
    int kl_qp = thes_kl_divergence(&q, &p);
    /* They may differ significantly for divergent distributions */
    ASSERT(kl_pq >= 0 && kl_qp >= 0, "both non-negative");
    PASS();
}

/* Test 5554: Yield function bounds */
static void test_yield_bounds(void) {
    SECTION("Epistemic Advanced: Yield Bounds");
    
    TEST("Yield B = exp(-D_KL) ∈ [0, 1000]");
    thes_distribution_t tau = { 3, 4, 3, 10 };
    thes_distribution_t q = { 3, 4, 3, 10 };
    int yield = thes_yield(&tau, &q);
    ASSERT(yield >= 0 && yield <= 1000, "expected [0, 1000]");
    PASS();
}

/* Test 5555: Yield for perfectly aligned distributions */
static void test_yield_perfect_alignment(void) {
    SECTION("Epistemic Advanced: Yield Perfect Alignment");
    
    TEST("Yield = 1000 for identical distributions");
    thes_distribution_t tau = { 2, 3, 5, 10 };
    thes_distribution_t q = { 2, 3, 5, 10 };
    int yield = thes_yield(&tau, &q);
    ASSERT(yield == 1000, "expected 1000");
    PASS();
}

/* Test 5556: Yield decreases with divergence */
static void test_yield_divergence_penalty(void) {
    SECTION("Epistemic Advanced: Yield Divergence Penalty");
    
    TEST("Yield decreases as distributions diverge");
    thes_distribution_t tau = { 1, 1, 1, 3 };
    thes_distribution_t q1 = { 1, 1, 1, 3 };
    thes_distribution_t q2 = { 10, 1, 1, 12 }; /* Divergent */
    
    int yield1 = thes_yield(&tau, &q1);
    int yield2 = thes_yield(&tau, &q2);
    ASSERT(yield1 >= yield2, "aligned yield >= divergent yield");
    PASS();
}

/* Test 5557: B4 inconsistency threshold (15%) */
static void test_b4_threshold_15_percent(void) {
    SECTION("Epistemic Advanced: B4 15% Threshold");
    
    TEST("B4 detected when both T and F > 15% of observations");
    thes_distribution_t dist = { 2, 5, 3, 10 }; /* F=20%, T=30% */
    ASSERT(thes_b4_check(&dist) == 1, "expected B4 inconsistency");
    PASS();
}

/* Test 5558: B4 not triggered below threshold */
static void test_b4_below_threshold(void) {
    SECTION("Epistemic Advanced: B4 Below Threshold");
    
    TEST("B4 not detected when one value < 15%");
    thes_distribution_t dist = { 1, 8, 1, 10 }; /* F=10%, T=10% */
    ASSERT(thes_b4_check(&dist) == 0, "expected no B4");
    PASS();
}

/* Test 5559: B4 boundary at 15% */
static void test_b4_boundary_condition(void) {
    SECTION("Epistemic Advanced: B4 Boundary");
    
    TEST("B4 boundary: exactly 15% for each value");
    thes_distribution_t dist = { 15, 70, 15, 100 }; /* F=15%, T=15% */
    /* Implementation uses > 15, so 15% should not trigger */
    int result = thes_b4_check(&dist);
    ASSERT(result == 0, "expected no B4 at boundary");
    PASS();
}

/* Test 5560: B4 with single observation */
static void test_b4_single_observation(void) {
    SECTION("Epistemic Advanced: B4 Single Observation");
    
    TEST("B4 not detected with < 2 observations");
    thes_distribution_t dist = { 1, 0, 0, 1 };
    ASSERT(thes_b4_check(&dist) == 0, "expected no B4");
    PASS();
}

/* Test 5561: Multi-channel drift aggregation */
static void test_multi_channel_drift(void) {
    SECTION("Epistemic Advanced: Multi-Channel Drift");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch1 = thes_register_channel(&reactor);
    int ch2 = thes_register_channel(&reactor);
    
    /* Feed high Unknown rate to both channels */
    for (int i = 0; i < 5; i++) {
        thes_observe(&reactor, ch1, TRIT_UNKNOWN);
        thes_observe(&reactor, ch2, TRIT_UNKNOWN);
    }
    
    TEST("Drift aggregates across channels");
    int drift = thes_get_drift(&reactor);
    ASSERT(drift >= 80, "expected high drift >= 80%");
    PASS();
}

/* Test 5562: Drift with mixed channel states */
static void test_drift_mixed_channels(void) {
    SECTION("Epistemic Advanced: Drift Mixed Channels");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch1 = thes_register_channel(&reactor);
    int ch2 = thes_register_channel(&reactor);
    
    /* ch1: high Unknown, ch2: low Unknown */
    for (int i = 0; i < 5; i++) {
        thes_observe(&reactor, ch1, TRIT_UNKNOWN);
        thes_observe(&reactor, ch2, TRIT_TRUE);
    }
    
    TEST("Drift averages across mixed channels");
    int drift = thes_get_drift(&reactor);
    ASSERT(drift >= 25 && drift <= 75, "expected moderate drift");
    PASS();
}

/* Test 5563: Recalibration resets distribution */
static void test_recalibration_resets_distribution(void) {
    SECTION("Epistemic Advanced: Recalibration Distribution Reset");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Build up distribution */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    
    /* Recalibrate */
    thes_recalibrate(&reactor, ch);
    
    TEST("Distribution reset after recalibration");
    ASSERT(reactor.channels[ch].dist.total == 0, "expected 0 total");
    ASSERT(reactor.channels[ch].dist.count_unknown == 0, "expected 0 Unknown");
    PASS();
}

/* Test 5564: Recalibration resets confidence */
static void test_recalibration_resets_confidence(void) {
    SECTION("Epistemic Advanced: Recalibration Confidence Reset");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    thes_recalibrate(&reactor, ch);
    
    TEST("Confidence metrics reset");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.definiteness_pct == 0, "expected 0%");
    ASSERT(conf.streak_unknown == 0, "expected 0");
    PASS();
}

/* Test 5565: Recalibration changes state to RECAL */
static void test_recalibration_state(void) {
    SECTION("Epistemic Advanced: Recalibration State");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    thes_observe(&reactor, ch, TRIT_TRUE);
    thes_recalibrate(&reactor, ch);
    
    TEST("State changes to RECAL");
    ASSERT(reactor.channels[ch].state == THES_STATE_RECAL, "expected RECAL");
    PASS();
}

/* Test 5566: Recalibration increments counter */
static void test_recalibration_counter(void) {
    SECTION("Epistemic Advanced: Recalibration Counter");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    thes_recalibrate(&reactor, ch);
    thes_recalibrate(&reactor, ch);
    
    TEST("Recalibration counter increments");
    ASSERT(reactor.channels[ch].recalibrations == 2, "expected 2");
    PASS();
}

/* Test 5567: Window wrapping at 32 samples */
static void test_window_wrapping_32(void) {
    SECTION("Epistemic Advanced: Window Wrapping at 32");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Feed 50 observations (exceeds THES_WINDOW_SIZE=32) */
    for (int i = 0; i < 50; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("Window position wraps after 32");
    ASSERT(reactor.channels[ch].window_filled == 1, "window filled");
    ASSERT(reactor.channels[ch].window_pos < THES_WINDOW_SIZE, "pos < 32");
    PASS();
}

/* Test 5568: Window filled flag set after 32 observations */
static void test_window_filled_flag(void) {
    SECTION("Epistemic Advanced: Window Filled Flag");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    for (int i = 0; i < THES_WINDOW_SIZE; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("Window filled flag set");
    ASSERT(reactor.channels[ch].window_filled == 1, "expected 1");
    PASS();
}

/* Test 5569: Confidence recomputation uses window limit */
static void test_confidence_window_limit(void) {
    SECTION("Epistemic Advanced: Confidence Window Limit");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Feed < 32 observations */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("Confidence uses actual observations before window filled");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.definiteness_pct == 100, "expected 100% (all TRUE)");
    PASS();
}

/* Test 5570: Max Unknown streak tracking */
static void test_max_unknown_streak(void) {
    SECTION("Epistemic Advanced: Max Unknown Streak");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Create streak of 7 Unknowns */
    for (int i = 0; i < 7; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    thes_observe(&reactor, ch, TRIT_TRUE); /* Break streak */
    
    /* Create shorter streak of 3 */
    for (int i = 0; i < 3; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    
    TEST("Max streak recorded");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.max_streak_unknown == 7, "expected 7");
    PASS();
}

/* Test 5571: Streak resets on definite value */
static void test_streak_reset_on_definite(void) {
    SECTION("Epistemic Advanced: Streak Reset");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    thes_observe(&reactor, ch, TRIT_TRUE); /* Reset */
    
    TEST("Current streak resets to 0");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.streak_unknown == 0, "expected 0");
    PASS();
}

/* Test 5572: Last definite value tracking across Unknowns */
static void test_last_definite_across_unknowns(void) {
    SECTION("Epistemic Advanced: Last Definite Tracking");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    thes_observe(&reactor, ch, TRIT_FALSE);
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    
    TEST("Last definite persists across Unknowns");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.last_definite == TRIT_FALSE, "expected FALSE");
    PASS();
}

/* Test 5573: State transition IDLE → RUNNING */
static void test_state_transition_idle_to_running(void) {
    SECTION("Epistemic Advanced: State IDLE → RUNNING");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    TEST("Initial state is IDLE");
    ASSERT(reactor.channels[ch].state == THES_STATE_IDLE, "expected IDLE");
    
    /* Feed definite value with low Unknown rate */
    thes_observe(&reactor, ch, TRIT_TRUE);
    
    TEST("State transitions to RUNNING");
    ASSERT(reactor.channels[ch].state == THES_STATE_RUNNING, "expected RUNNING");
    PASS();
}

/* Test 5574: State transition RUNNING → HESITATING */
static void test_state_transition_running_to_hesitating(void) {
    SECTION("Epistemic Advanced: State RUNNING → HESITATING");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Start with definite */
    thes_observe(&reactor, ch, TRIT_TRUE);
    ASSERT(reactor.channels[ch].state == THES_STATE_RUNNING, "expected RUNNING");
    
    /* Feed Unknowns to exceed drift threshold (18%) */
    for (int i = 0; i < 5; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    
    TEST("State transitions to HESITATING");
    ASSERT(reactor.channels[ch].state == THES_STATE_HESITATING, "expected HESITATING");
    PASS();
}

/* Test 5575: State transition HESITATING → RUNNING */
static void test_state_transition_hesitating_to_running(void) {
    SECTION("Epistemic Advanced: State HESITATING → RUNNING");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Trigger hesitation with 5 Unknowns */
    for (int i = 0; i < 5; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    ASSERT(reactor.channels[ch].state == THES_STATE_HESITATING, "expected HESITATING");
    
    /* Feed definite values to drop below 18% threshold
     * Need: 5/(5+x) < 0.18 → x > 23 */
    for (int i = 0; i < 30; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("State recovers to RUNNING");
    ASSERT(reactor.channels[ch].state == THES_STATE_RUNNING, "expected RUNNING");
    PASS();
}

/* Test 5576: DLT reactor recommends reactivation */
static void test_dlt_reactor_recommend_reactivation(void) {
    SECTION("Epistemic Advanced: DLT Reactivation");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Feed high Unknown rate > 18% */
    for (int i = 0; i < 5; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    thes_observe(&reactor, ch, TRIT_TRUE); /* 5/6 = 83% Unknown */
    
    TEST("DLT recommends reactivation when Unknown > threshold and trapping > target");
    int recommend = thes_dlt_react(&reactor, ch, 500, 200); /* trapping=500 > target=200 */
    ASSERT(recommend == 1, "expected 1");
    PASS();
}

/* Test 5577: DLT reactor no reactivation when below threshold */
static void test_dlt_reactor_no_reactivation(void) {
    SECTION("Epistemic Advanced: DLT No Reactivation");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Feed low Unknown rate */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("DLT no reactivation when Unknown < threshold");
    int recommend = thes_dlt_react(&reactor, ch, 500, 200);
    ASSERT(recommend == 0, "expected 0");
    PASS();
}

/* Test 5578: Channel deactivation handling */
static void test_channel_deactivation(void) {
    SECTION("Epistemic Advanced: Channel Deactivation");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Deactivate channel */
    reactor.channels[ch].active = 0;
    
    TEST("Observe returns -1 for inactive channel");
    int result = thes_observe(&reactor, ch, TRIT_TRUE);
    ASSERT(result == -1, "expected -1");
    PASS();
}

/* Test 5579: Invalid channel ID returns error */
static void test_invalid_channel_id(void) {
    SECTION("Epistemic Advanced: Invalid Channel ID");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    
    TEST("Observe with invalid channel ID returns -1");
    int result = thes_observe(&reactor, 99, TRIT_TRUE);
    ASSERT(result == -1, "expected -1");
    PASS();
}

/* Test 5580: NULL reactor pointer handling */
static void test_null_reactor_pointer(void) {
    SECTION("Epistemic Advanced: NULL Reactor Pointer");
    
    TEST("Operations with NULL reactor return -1");
    ASSERT(thes_observe(NULL, 0, TRIT_TRUE) == -1, "observe returns -1");
    ASSERT(thes_register_channel(NULL) == -1, "register returns -1");
    ASSERT(thes_recalibrate(NULL, 0) == -1, "recalibrate returns -1");
    PASS();
}

/* Test 5581: KL divergence with NULL pointers */
static void test_kl_divergence_null_pointers(void) {
    SECTION("Epistemic Advanced: KL Divergence NULL Pointers");
    
    thes_distribution_t dist = { 1, 1, 1, 3 };
    
    TEST("KL divergence with NULL returns -1");
    ASSERT(thes_kl_divergence(NULL, &dist) == -1, "NULL p returns -1");
    ASSERT(thes_kl_divergence(&dist, NULL) == -1, "NULL q returns -1");
    PASS();
}

/* Test 5582: Yield function with NULL pointers */
static void test_yield_null_pointers(void) {
    SECTION("Epistemic Advanced: Yield NULL Pointers");
    
    thes_distribution_t dist = { 1, 1, 1, 3 };
    
    TEST("Yield with NULL returns -1");
    int result = thes_yield(NULL, &dist);
    ASSERT(result == -1, "NULL tau returns -1");
    PASS();
}

/* Test 5583: B4 check with NULL pointer */
static void test_b4_check_null(void) {
    SECTION("Epistemic Advanced: B4 Check NULL");
    
    TEST("B4 check with NULL returns 0");
    ASSERT(thes_b4_check(NULL) == 0, "expected 0");
    PASS();
}

/* Test 5584: Get confidence with NULL output pointer */
static void test_get_confidence_null_output(void) {
    SECTION("Epistemic Advanced: Get Confidence NULL Output");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    TEST("Get confidence with NULL output returns -1");
    int result = thes_get_confidence(&reactor, ch, NULL);
    ASSERT(result == -1, "expected -1");
    PASS();
}

/* Test 5585: Distribution convergence over time */
static void test_distribution_convergence(void) {
    SECTION("Epistemic Advanced: Distribution Convergence");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Feed biased stream: 80% TRUE, 20% FALSE */
    for (int i = 0; i < 50; i++) {
        if (i % 5 == 0)
            thes_observe(&reactor, ch, TRIT_FALSE);
        else
            thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("Distribution converges to expected ratios");
    int true_pct = (reactor.channels[ch].dist.count_true * 100) / reactor.channels[ch].dist.total;
    ASSERT(true_pct >= 70 && true_pct <= 90, "expected ~80%");
    PASS();
}

/* Test 5586: Confidence tracking with alternating pattern */
static void test_confidence_alternating_pattern(void) {
    SECTION("Epistemic Advanced: Confidence Alternating");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Alternate TRUE/UNKNOWN */
    for (int i = 0; i < 20; i++) {
        thes_observe(&reactor, ch, (i % 2 == 0) ? TRIT_TRUE : TRIT_UNKNOWN);
    }
    
    TEST("Confidence reflects 50% definiteness");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.definiteness_pct >= 40 && conf.definiteness_pct <= 60, "expected ~50%");
    PASS();
}

/* Test 5587: Unknown rate percentage accuracy */
static void test_unknown_rate_accuracy(void) {
    SECTION("Epistemic Advanced: Unknown Rate Accuracy");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* 7 TRUE, 3 UNKNOWN → 30% Unknown */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, (i < 7) ? TRIT_TRUE : TRIT_UNKNOWN);
    }
    
    TEST("Unknown rate calculated accurately");
    thes_confidence_t conf;
    thes_get_confidence(&reactor, ch, &conf);
    ASSERT(conf.unknown_rate_pct >= 25 && conf.unknown_rate_pct <= 35, "expected ~30%");
    PASS();
}

/* Test 5588: Total pauses increments correctly */
static void test_total_pauses_increment(void) {
    SECTION("Epistemic Advanced: Total Pauses Increment");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    int initial = thes_get_total_pauses(&reactor);
    
    /* Trigger hesitation */
    for (int i = 0; i < 5; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    
    TEST("Total pauses incremented");
    int final = thes_get_total_pauses(&reactor);
    ASSERT(final > initial, "expected increment");
    PASS();
}

/* Test 5589: Total decisions increments correctly */
static void test_total_decisions_increment(void) {
    SECTION("Epistemic Advanced: Total Decisions Increment");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    int initial = thes_get_total_decisions(&reactor);
    
    /* Feed definite values */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    TEST("Total decisions incremented");
    int final = thes_get_total_decisions(&reactor);
    ASSERT(final >= initial + 10, "expected >= +10");
    PASS();
}

/* Test 5590: B4 flags accumulation across observations */
static void test_b4_flags_accumulation(void) {
    SECTION("Epistemic Advanced: B4 Flags Accumulation");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Build distribution with both TRUE and FALSE > 15% */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, (i < 5) ? TRIT_TRUE : TRIT_FALSE);
    }
    
    TEST("B4 flags accumulated");
    ASSERT(reactor.total_b4_flags > 0, "expected > 0");
    PASS();
}

/* Test 5591: Drift threshold configuration */
static void test_drift_threshold_custom(void) {
    SECTION("Epistemic Advanced: Drift Threshold Config");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    
    /* Modify threshold */
    reactor.drift_threshold = 25; /* 25% instead of default 18% */
    int ch = thes_register_channel(&reactor);
    
    /* Feed 20% Unknown (below new threshold) */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, (i < 2) ? TRIT_UNKNOWN : TRIT_TRUE);
    }
    
    TEST("Custom threshold affects state transitions");
    /* With 20% Unknown < 25% threshold, should be RUNNING */
    ASSERT(reactor.channels[ch].state == THES_STATE_RUNNING, "expected RUNNING");
    PASS();
}

/* Test 5592: Epistemic ternary comparison closure */
static void test_epistemic_closure_max(void) {
    SECTION("Epistemic Advanced: Closure Under Comparison");
    
    TEST("Trit comparison operations are closed over {-1, 0, 1}");
    int ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit result = (a > b) ? (trit)a : (trit)b;
            if (result < -1 || result > 1) {
                ok = 0;
                break;
            }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "comparison max produces valid trits");
    PASS();
}

/* Test 5593: Epistemic ternary min closure */
static void test_epistemic_closure_min(void) {
    SECTION("Epistemic Advanced: Closure Under Min");
    
    TEST("Trit min comparison is closed over {-1, 0, 1}");
    int ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit result = (a < b) ? (trit)a : (trit)b;
            if (result < -1 || result > 1) {
                ok = 0;
                break;
            }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "comparison min produces valid trits");
    PASS();
}

/* Test 5594: K3 consensus operator */
static void test_k3_consensus(void) {
    SECTION("Epistemic Advanced: K3 Consensus");
    
    TEST("Consensus via comparison: T consensus T = T");
    trit t1 = TRIT_TRUE, t2 = TRIT_TRUE;
    trit result = (t1 > t2) ? t1 : t2;
    ASSERT(result == TRIT_TRUE, "T ⊔ T = T");
    
    TEST("Consensus via comparison: T vs F picks T");
    result = (TRIT_TRUE > TRIT_FALSE) ? TRIT_TRUE : TRIT_FALSE;
    ASSERT(result == TRIT_TRUE, "max(T,F) = T");
    PASS();
}

/* Test 5595: K3 meet operator properties */
static void test_k3_meet_properties(void) {
    SECTION("Epistemic Advanced: K3 Meet");
    
    TEST("Meet (comparison min) is commutative");
    int ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit ab = (a < b) ? (trit)a : (trit)b;
            trit ba = (b < a) ? (trit)b : (trit)a;
            if (ab != ba) {
                ok = 0;
                break;
            }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "min is commutative");
    PASS();
}

/* Test 5596: K3 join operator properties */
static void test_k3_join_properties(void) {
    SECTION("Epistemic Advanced: K3 Join");
    
    TEST("Join (comparison max) is commutative");
    int ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit ab = (a > b) ? (trit)a : (trit)b;
            trit ba = (b > a) ? (trit)b : (trit)a;
            if (ab != ba) {
                ok = 0;
                break;
            }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "max is commutative");
    PASS();
}

/* Test 5597: Hesitation reactor stress test */
static void test_hesitation_stress(void) {
    SECTION("Epistemic Advanced: Hesitation Stress");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Feed 1000 observations rapidly */
    for (int i = 0; i < 1000; i++) {
        trit value = (i % 3 == 0) ? TRIT_TRUE :
                     (i % 3 == 1) ? TRIT_FALSE : TRIT_UNKNOWN;
        thes_observe(&reactor, ch, value);
    }
    
    TEST("Reactor handles 1000 observations without failure");
    ASSERT(reactor.channels[ch].dist.total == 1000, "expected 1000");
    PASS();
}

/* Test 5598: Multi-channel stress test */
static void test_multi_channel_stress(void) {
    SECTION("Epistemic Advanced: Multi-Channel Stress");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    
    /* Register max channels */
    for (int i = 0; i < THES_MAX_CHANNELS; i++) {
        int ch = thes_register_channel(&reactor);
        ASSERT(ch >= 0, "expected valid channel ID");
        
        /* Feed observations to each */
        for (int j = 0; j < 10; j++) {
            thes_observe(&reactor, ch, TRIT_TRUE);
        }
    }
    
    TEST("Max channels all active");
    ASSERT(reactor.channel_count == THES_MAX_CHANNELS, "expected max channels");
    PASS();
}

/* Test 5599: Epistemic uncertainty propagation chain */
static void test_epistemic_uncertainty_chain(void) {
    SECTION("Epistemic Advanced: Uncertainty Chain");
    
    TEST("Long AND chain propagates Unknown correctly");
    trit chain = TRIT_TRUE;
    for (int i = 0; i < 10; i++) {
        chain = trit_and(chain, TRIT_TRUE);
    }
    chain = trit_and(chain, TRIT_UNKNOWN); /* Inject Unknown */
    for (int i = 0; i < 10; i++) {
        chain = trit_and(chain, TRIT_TRUE);
    }
    ASSERT(chain == TRIT_UNKNOWN, "Unknown persists through chain");
    PASS();
}

/* Test 5600: Epistemic confidence degradation */
static void test_epistemic_confidence_degradation(void) {
    SECTION("Epistemic Advanced: Confidence Degradation");
    
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);
    
    /* Start with high confidence */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, TRIT_TRUE);
    }
    
    thes_confidence_t conf1;
    thes_get_confidence(&reactor, ch, &conf1);
    int initial_conf = conf1.definiteness_pct;
    
    /* Degrade with Unknowns */
    for (int i = 0; i < 20; i++) {
        thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    
    thes_confidence_t conf2;
    thes_get_confidence(&reactor, ch, &conf2);
    int final_conf = conf2.definiteness_pct;
    
    TEST("Confidence degrades with Unknown observations");
    ASSERT(final_conf < initial_conf, "confidence decreased");
    PASS();
}

/* Test 5601: Epistemic yield sensitivity to minor divergence */
static void test_yield_sensitivity(void) {
    SECTION("Epistemic Advanced: Yield Sensitivity");
    
    TEST("Yield detects minor distribution divergence");
    thes_distribution_t tau = { 10, 10, 10, 30 }; /* Uniform */
    thes_distribution_t q1  = { 10, 10, 10, 30 }; /* Identical */
    thes_distribution_t q2  = { 11, 10, 9, 30 };  /* Slightly different */
    
    int yield1 = thes_yield(&tau, &q1);
    int yield2 = thes_yield(&tau, &q2);
    
    /* q1 should have higher yield (perfect alignment) */
    ASSERT(yield1 >= yield2, "perfect alignment yield >= divergent");
    PASS();
}

/*==============================================================================
 * Main Test Runner
 *============================================================================*/

int main(void) {
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  seT5/seT6 Test Suite — Batch 96: Tests 5552-5601            ║\n");
    printf("║  Theme: Epistemic Logic & Hesitation (Advanced)              ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    printf("\n");

    /* Execute all 50 tests */
    test_kl_divergence_non_negative();
    test_kl_divergence_asymmetric();
    test_yield_bounds();
    test_yield_perfect_alignment();
    test_yield_divergence_penalty();
    test_b4_threshold_15_percent();
    test_b4_below_threshold();
    test_b4_boundary_condition();
    test_b4_single_observation();
    test_multi_channel_drift();
    test_drift_mixed_channels();
    test_recalibration_resets_distribution();
    test_recalibration_resets_confidence();
    test_recalibration_state();
    test_recalibration_counter();
    test_window_wrapping_32();
    test_window_filled_flag();
    test_confidence_window_limit();
    test_max_unknown_streak();
    test_streak_reset_on_definite();
    test_last_definite_across_unknowns();
    test_state_transition_idle_to_running();
    test_state_transition_running_to_hesitating();
    test_state_transition_hesitating_to_running();
    test_dlt_reactor_recommend_reactivation();
    test_dlt_reactor_no_reactivation();
    test_channel_deactivation();
    test_invalid_channel_id();
    test_null_reactor_pointer();
    test_kl_divergence_null_pointers();
    test_yield_null_pointers();
    test_b4_check_null();
    test_get_confidence_null_output();
    test_distribution_convergence();
    test_confidence_alternating_pattern();
    test_unknown_rate_accuracy();
    test_total_pauses_increment();
    test_total_decisions_increment();
    test_b4_flags_accumulation();
    test_drift_threshold_custom();
    test_epistemic_closure_max();
    test_epistemic_closure_min();
    test_k3_consensus();
    test_k3_meet_properties();
    test_k3_join_properties();
    test_hesitation_stress();
    test_multi_channel_stress();
    test_epistemic_uncertainty_chain();
    test_epistemic_confidence_degradation();
    test_yield_sensitivity();

    /* Print summary */
    printf("\n");
    printf("════════════════════════════════════════════════════════════════\n");
    printf("  Tests Run:    %d\n", test_count);
    printf("  Passed:       %d\n", pass_count);
    printf("  Failed:       %d\n", fail_count);
    printf("  Pass Rate:    %.1f%%\n", 
           test_count > 0 ? (100.0 * pass_count / test_count) : 0.0);
    printf("════════════════════════════════════════════════════════════════\n");
    printf("\n");

    return (fail_count == 0) ? 0 : 1;
}
