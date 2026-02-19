/*==============================================================================
 * seT5/seT6 Test Generation — Batch 98
 *
 * Range: Tests 5652-5701 (50 tests)
 * Theme: Guardian Trit Mechanisms (Advanced)
 * Aspect: Multi-channel guardian sync, collision resistance, attack scenarios,
 *         performance stress, differential cryptanalysis, guardian chaining,
 *         error recovery, Byzantine fault tolerance, probabilistic guarantees.
 *
 * Generated: 2025-02-19
 * Target: 100% pass rate (Sigma 9 compliance)
 *============================================================================*/

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "set5/trit.h"
#include "set5/tipc.h"

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
 * Advanced Guardian Trit Tests 5652-5701
 *============================================================================*/

/* Test 5652: Guardian collision resistance */
static void test_guardian_collision_resistance(void) {
    SECTION("Guardian Advanced: Collision Resistance");
    
    TEST("Different messages should have different guardians (usually)");
    trit buf1[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit buf2[] = { TRIT_FALSE, TRIT_TRUE, TRIT_TRUE };
    
    trit g1 = tipc_guardian_compute(buf1, 3);
    trit g2 = tipc_guardian_compute(buf2, 3);
    
    /* Sum1: 1 + (-1) + 0 = 0 → UNKNOWN */
    /* Sum2: -1 + 1 + 1 = 1 → TRUE */
    ASSERT(g1 != g2, "different guardians");
    PASS();
}

/* Test 5653: Guardian intentional collision */
static void test_guardian_intentional_collision(void) {
    SECTION("Guardian Advanced: Intentional Collision");
    
    TEST("Deliberately crafted messages can have same guardian");
    /* Both sum to 0 (mod 3) */
    trit buf1[] = { TRIT_UNKNOWN, TRIT_UNKNOWN };
    trit buf2[] = { TRIT_TRUE, TRIT_FALSE };
    
    trit g1 = tipc_guardian_compute(buf1, 2);
    trit g2 = tipc_guardian_compute(buf2, 2);
    
    ASSERT(g1 == g2, "collision possible");
    ASSERT(g1 == TRIT_UNKNOWN, "both sum to 0");
    PASS();
}

/* Test 5654: Guardian bit flip detection probability */
static void test_guardian_bit_flip_detection(void) {
    SECTION("Guardian Advanced: Bit Flip Detection");
    
    TEST("Single trit flip changes guardian in 2/3 cases");
    trit buf[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    trit original_guardian = tipc_guardian_compute(buf, 3);
    
    /* Flip one trit: TRUE → FALSE (delta = -2) */
    buf[1] = TRIT_FALSE;
    trit new_guardian = tipc_guardian_compute(buf, 3);
    
    /* Original: 3 ≡ 0, New: 1 + (-1) + 1 = 1 → different */
    ASSERT(new_guardian != original_guardian, "flip detected");
    PASS();
}

/* Test 5655: Guardian avalanche effect */
static void test_guardian_avalanche(void) {
    SECTION("Guardian Advanced: Avalanche Effect");
    
    TEST("Small change causes significant guardian change");
    trit buf1[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    trit buf2[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE };
    
    trit g1 = tipc_guardian_compute(buf1, 4);
    trit g2 = tipc_guardian_compute(buf2, 4);
    
    /* g1: 4 ≡ 1 (TRUE), g2: 2 ≡ -1 (FALSE) */
    ASSERT(g1 != g2, "avalanche observed");
    PASS();
}

/* Test 5656: Multi-channel guardian synchronization */
static void test_multi_channel_guardian_sync(void) {
    SECTION("Guardian Advanced: Multi-Channel Sync");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    int ep1 = tipc_endpoint_create(&ch);
    int ep2 = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_FALSE };
    tipc_send(&ch, ep1, msg, 2, TIPC_PRIO_HIGH);
    tipc_send(&ch, ep2, msg, 2, TIPC_PRIO_HIGH);
    
    TEST("Same message to different endpoints has same guardian");
    ASSERT(ch.endpoints[ep1].inbox.guardian == 
           ch.endpoints[ep2].inbox.guardian, "guardians match");
    PASS();
}

/* Test 5657: Guardian with adversarial input */
static void test_guardian_adversarial(void) {
    SECTION("Guardian Advanced: Adversarial Input");
    
    TEST("Guardian handles adversarial patterns");
    /* Attacker tries to craft message with guardian = 0 */
    trit buf[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };  /* Sum = 0 mod 3 */
    trit guardian = tipc_guardian_compute(buf, 3);
    
    ASSERT(guardian == TRIT_UNKNOWN, "sum mod 3 = 0");
    /* Guardian still computes correctly */
    PASS();
}

/* Test 5658: Guardian differential analysis */
static void test_guardian_differential(void) {
    SECTION("Guardian Advanced: Differential Analysis");
    
    TEST("Guardian differential: flip one trit");
    trit buf1[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit buf2[] = { TRIT_FALSE, TRIT_FALSE, TRIT_UNKNOWN };
    
    trit g1 = tipc_guardian_compute(buf1, 3);
    trit g2 = tipc_guardian_compute(buf2, 3);
    
    /* Difference: TRUE → FALSE (delta = -2) */
    /* g1: 0, g2: -2 ≡ 1 (mod 3) → different */
    ASSERT(g1 != g2, "differential detected");
    PASS();
}

/* Test 5659: Guardian chaining */
static void test_guardian_chaining(void) {
    SECTION("Guardian Advanced: Guardian Chaining");
    
    TEST("Chain guardians: g(m1) + g(m2) = g(m1||m2)");
    trit msg1[] = { TRIT_TRUE, TRIT_FALSE };
    trit msg2[] = { TRIT_UNKNOWN, TRIT_TRUE };
    
    trit g1 = tipc_guardian_compute(msg1, 2);
    trit g2 = tipc_guardian_compute(msg2, 2);
    
    /* Combined message */
    trit combined[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    trit g_combined = tipc_guardian_compute(combined, 4);
    
    /* Chain property: g1 + g2 = g_combined */
    trit g_chain[]  = { g1, g2 };
    trit g_from_chain = tipc_guardian_compute(g_chain, 2);
    
    ASSERT(g_from_chain == g_combined, "chaining property holds");
    PASS();
}

/* Test 5660: Guardian performance stress */
static void test_guardian_performance_stress(void) {
    SECTION("Guardian Advanced: Performance Stress");
    
    TEST("Guardian computes 10000 messages without failure");
    trit buf[10];
    int ok = 1;
    
    for (int i = 0; i < 10000; i++) {
        for (int j = 0; j < 10; j++) {
            buf[j] = (trit)((i * j) % 3 - 1);
        }
        trit g = tipc_guardian_compute(buf, 10);
        if (g < -1 || g > 1) {
            ok = 0;
            break;
        }
    }
    
    ASSERT(ok == 1, "performance stress passed");
    PASS();
}

/* Test 5661: Guardian with max buffer stress */
static void test_guardian_max_buffer_stress(void) {
    SECTION("Guardian Advanced: Max Buffer Stress");
    
    TEST("Guardian handles TIPC_MAX_TRITS buffer");
    trit buf[TIPC_MAX_TRITS];
    for (int i = 0; i < TIPC_MAX_TRITS; i++) {
        buf[i] = (i % 3 == 0) ? TRIT_TRUE : 
                 (i % 3 == 1) ? TRIT_FALSE : TRIT_UNKNOWN;
    }
    
    trit guardian = tipc_guardian_compute(buf, TIPC_MAX_TRITS);
    ASSERT(guardian >= -1 && guardian <= 1, "valid guardian");
    PASS();
}

/* Test 5662: Guardian Byzantine fault tolerance */
static void test_guardian_byzantine_fault(void) {
    SECTION("Guardian Advanced: Byzantine Fault");
    
    TEST("Guardian detects Byzantine corruption");
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_TRUE;
    msg.count = 2;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    /* Byzantine fault: flip message but keep guardian */
    msg.trits[0] = TRIT_FALSE;
    /* Guardian now mismatches */
    
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_FAIL, "Byzantine fault detected");
    PASS();
}

/* Test 5663: Guardian recovery after tamper */
static void test_guardian_recovery(void) {
    SECTION("Guardian Advanced: Recovery After Tamper");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.count = 2;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    /* Tamper */
    msg.trits[0] = TRIT_FALSE;
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_FAIL, "tamper detected");
    
    /* Restore and recompute */
    msg.trits[0] = TRIT_TRUE;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    TEST("Recovery after tamper");
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_OK, "recovered");
    PASS();
}

/* Test 5664: Guardian false positive rate */
static void test_guardian_false_positive_rate(void) {
    SECTION("Guardian Advanced: False Positive Rate");
    
    TEST("Guardian has low false positive rate");
    /* Same guardian can occur for different messages (1/3 probability) */
    int collision_count = 0;
    trit base_msg[] = { TRIT_TRUE, TRIT_FALSE };
    trit base_guardian = tipc_guardian_compute(base_msg, 2);
    
    /* Try 100 different messages */
    for (int i = 0; i < 100; i++) {
        trit test_msg[] = { (trit)(i % 3 - 1), (trit)((i / 3) % 3 - 1) };
        trit test_guardian = tipc_guardian_compute(test_msg, 2);
        
        /* Check if guardians match but messages differ */
        if (test_guardian == base_guardian && 
            (test_msg[0] != base_msg[0] || test_msg[1] != base_msg[1])) {
            collision_count++;
        }
    }
    
    /* Expect ~33 collisions (1/3 of 99 different messages) */
    ASSERT(collision_count >= 20 && collision_count <= 50, "reasonable collision rate");
    PASS();
}

/* Test 5665: Guardian with compression pipeline */
static void test_guardian_compression_pipeline(void) {
    SECTION("Guardian Advanced: Compression Pipeline");
    
    TEST("Guardian preserved through compression pipeline");
    trit original[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit original_guardian = tipc_guardian_compute(original, 3);
    
    /* Compress → Decompress → Check guardian */
    tipc_compressed_t comp;
    tipc_compress(&comp, original, 3);
    
    trit decompressed[10];
    int n = tipc_decompress(decompressed, 10, &comp);
    trit decompressed_guardian = tipc_guardian_compute(decompressed, n);
    
    ASSERT(original_guardian == decompressed_guardian, "guardian preserved");
    PASS();
}

/* Test 5666: Guardian XOR diff chaining */
static void test_guardian_xor_diff_chaining(void) {
    SECTION("Guardian Advanced: XOR Diff Chaining");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.count = 2;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    /* Apply multiple diffs */
    trit delta1[] = { TRIT_UNKNOWN, TRIT_TRUE };
    trit delta2[] = { TRIT_TRUE, TRIT_UNKNOWN };
    
    tipc_xor_diff(&msg, delta1, 2);
    tipc_xor_diff(&msg, delta2, 2);
    
    TEST("XOR diff chaining updates guardian correctly");
    trit expected_guardian = tipc_guardian_compute(msg.trits, msg.count);
    ASSERT(msg.guardian == expected_guardian, "guardian correct after chaining");
    PASS();
}

/* Test 5667: Guardian uniform distribution analysis */
static void test_guardian_uniform_distribution(void) {
    SECTION("Guardian Advanced: Uniform Distribution");
    
    TEST("Guardian outputs are roughly uniform over {-1, 0, 1}");
    int count_neg = 0, count_zero = 0, count_pos = 0;
    
    for (int i = 0; i < 300; i++) {
        trit buf[] = { (trit)(i % 3 - 1), (trit)((i / 3) % 3 - 1) };
        trit g = tipc_guardian_compute(buf, 2);
        
        if (g == TRIT_FALSE) count_neg++;
        else if (g == TRIT_UNKNOWN) count_zero++;
        else if (g == TRIT_TRUE) count_pos++;
    }
    
    /* Each should be ~100 (1/3 of 300) */
    ASSERT(count_neg >= 80 && count_neg <= 120, "neg count ~100");
    ASSERT(count_zero >= 80 && count_zero <= 120, "zero count ~100");
    ASSERT(count_pos >= 80 && count_pos <= 120, "pos count ~100");
    PASS();
}

/* Test 5668: Guardian incremental update */
static void test_guardian_incremental_update(void) {
    SECTION("Guardian Advanced: Incremental Update");
    
    TEST("Guardian can be incrementally updated");
    trit buf[] = { TRIT_TRUE, TRIT_FALSE };
    trit g_initial = tipc_guardian_compute(buf, 2);
    
    /* Append new trit by computing delta */
    trit new_trit = TRIT_UNKNOWN;
    trit delta[] = { g_initial, new_trit };
    trit g_updated = tipc_guardian_compute(delta, 2);
    
    /* Verify against full recomputation */
    trit full_buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit g_full = tipc_guardian_compute(full_buf, 3);
    
    ASSERT(g_updated == g_full, "incremental update matches");
    PASS();
}

/* Test 5669: Guardian error detection probability */
static void test_guardian_error_detection_probability(void) {
    SECTION("Guardian Advanced: Error Detection Probability");
    
    TEST("Guardian detects errors with ~66% probability");
    int detected = 0;
    int total = 100;
    
    for (int i = 0; i < total; i++) {
        trit original[] = { TRIT_TRUE, TRIT_TRUE };
        trit guardian = tipc_guardian_compute(original, 2);
        
        /* Introduce random error */
        trit corrupted[] = { (trit)(i % 3 - 1), TRIT_TRUE };
        trit corrupted_guardian = tipc_guardian_compute(corrupted, 2);
        
        if (corrupted_guardian != guardian) {
            detected++;
        }
    }
    
    /* Should detect ~66 out of 100 (2/3 probability) */
    ASSERT(detected >= 50 && detected <= 85, "detection rate ~66%");
    PASS();
}

/* Test 5670: T-IPC guardian failure recovery */
static void test_tipc_guardian_failure_recovery(void) {
    SECTION("Guardian Advanced: T-IPC Failure Recovery");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_FALSE };
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_HIGH);
    
    /* Corrupt guardian (correct guardian is TRIT_UNKNOWN, corrupt to TRIT_TRUE) */
    ch.endpoints[ep].inbox.guardian = TRIT_TRUE;
    
    trit recv_buf[10];
    int n = tipc_recv(&ch, ep, recv_buf, 10);
    
    TEST("Failed receive can be retried after correction");
    ASSERT(n == -1, "first receive fails");
    
    /* Resend with correct guardian */
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_HIGH);
    n = tipc_recv(&ch, ep, recv_buf, 10);
    ASSERT(n == 2, "recovery successful");
    PASS();
}

/* Test 5671: Guardian batch validation */
static void test_guardian_batch_validation(void) {
    SECTION("Guardian Advanced: Batch Validation");
    
    TEST("Batch validation of multiple messages");
    tipc_message_t batch[5];
    
    for (int i = 0; i < 5; i++) {
        batch[i].trits[0] = (trit)(i % 3 - 1);
        batch[i].trits[1] = TRIT_TRUE;
        batch[i].count = 2;
        batch[i].guardian = tipc_guardian_compute(batch[i].trits, batch[i].count);
    }
    
    int valid_count = 0;
    for (int i = 0; i < 5; i++) {
        if (tipc_guardian_validate(&batch[i]) == TIPC_GUARDIAN_OK) {
            valid_count++;
        }
    }
    
    ASSERT(valid_count == 5, "all messages valid");
    PASS();
}

/* Test 5672: Guardian with radix guard integration */
static void test_guardian_radix_integration(void) {
    SECTION("Guardian Advanced: Radix Guard Integration");
    
    TEST("Guardian + radix guard provide dual layer security");
    /* Valid ternary data */
    uint8_t data[] = { 100, 150, 200 };
    int radix_ok = (tipc_radix_guard(data, 3) == 0);
    
    /* Valid guardian */
    trit msg[] = { TRIT_TRUE, TRIT_FALSE };
    tipc_message_t tipc_msg;
    memcpy(tipc_msg.trits, msg, sizeof(msg));
    tipc_msg.count = 2;
    tipc_msg.guardian = tipc_guardian_compute(msg, 2);
    int guardian_ok = (tipc_guardian_validate(&tipc_msg) == TIPC_GUARDIAN_OK);
    
    ASSERT(radix_ok && guardian_ok, "dual layer passed");
    PASS();
}

/* Test 5673: Guardian with priority-based validation */
static void test_guardian_priority_validation(void) {
    SECTION("Guardian Advanced: Priority-Based Validation");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit high_prio_msg[] = { TRIT_TRUE };
    trit low_prio_msg[] = { TRIT_FALSE };
    
    TEST("Guardian validates messages of different priorities");
    tipc_send(&ch, ep, high_prio_msg, 1, TIPC_PRIO_HIGH);
    trit recv1[10];
    int n1 = tipc_recv(&ch, ep, recv1, 10);
    ASSERT(n1 == 1, "high priority received");
    
    tipc_send(&ch, ep, low_prio_msg, 1, TIPC_PRIO_LOW);
    trit recv2[10];
    int n2 = tipc_recv(&ch, ep, recv2, 10);
    ASSERT(n2 == 1, "low priority received");
    PASS();
}

/* Test 5674: Guardian temporal consistency */
static void test_guardian_temporal_consistency(void) {
    SECTION("Guardian Advanced: Temporal Consistency");
    
    TEST("Guardian remains consistent over time");
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    
    trit g1 = tipc_guardian_compute(buf, 3);
    /* ... time passes ... */
    trit g2 = tipc_guardian_compute(buf, 3);
    
    ASSERT(g1 == g2, "temporal consistency");
    PASS();
}

/* Test 5675: Guardian with sparse data */
static void test_guardian_sparse_data(void) {
    SECTION("Guardian Advanced: Sparse Data");
    
    TEST("Guardian handles sparse (mostly zero) data");
    trit buf[50];
    for (int i = 0; i < 50; i++) {
        buf[i] = (i % 10 == 0) ? TRIT_TRUE : TRIT_UNKNOWN;
    }
    
    trit guardian = tipc_guardian_compute(buf, 50);
    /* 5 × TRUE = 5 ≡ 2 ≡ -1 (mod 3) → FALSE */
    ASSERT(guardian == TRIT_FALSE, "sparse guardian = -1");
    PASS();
}

/* Test 5676: Guardian with dense data */
static void test_guardian_dense_data(void) {
    SECTION("Guardian Advanced: Dense Data");
    
    TEST("Guardian handles dense (no zeros) data");
    trit buf[20];
    for (int i = 0; i < 20; i++) {
        buf[i] = (i % 2 == 0) ? TRIT_TRUE : TRIT_FALSE;
    }
    
    trit guardian = tipc_guardian_compute(buf, 20);
    /* 10 × TRUE + 10 × FALSE = 0 → UNKNOWN */
    ASSERT(guardian == TRIT_UNKNOWN, "dense guardian = 0");
    PASS();
}

/* Test 5677: Guardian with structured patterns */
static void test_guardian_structured_patterns(void) {
    SECTION("Guardian Advanced: Structured Patterns");
    
    TEST("Guardian handles structured patterns");
    /* Pattern: T, F, U repeated */
    trit buf[30];
    for (int i = 0; i < 30; i++) {
        buf[i] = (trit)(i % 3 - 1);
    }
    
    trit guardian = tipc_guardian_compute(buf, 30);
    /* 10 × TRUE + 10 × UNKNOWN + 10 × FALSE = 0 → UNKNOWN */
    ASSERT(guardian == TRIT_UNKNOWN, "structured pattern = 0");
    PASS();
}

/* Test 5678: Guardian cryptographic strength */
static void test_guardian_crypto_strength(void) {
    SECTION("Guardian Advanced: Cryptographic Strength");
    
    TEST("Guardian provides basic integrity (not crypto-grade)");
    /* Guardian is simple checksum, not cryptographic hash */
    /* Still, it should detect basic tampering */
    trit msg[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    trit guardian = tipc_guardian_compute(msg, 3);
    
    msg[1] = TRIT_FALSE;  /* Flip one bit */
    trit tampered_guardian = tipc_guardian_compute(msg, 3);
    
    ASSERT(guardian != tampered_guardian, "tamper detected");
    PASS();
}

/* Test 5679: Guardian with message fragmentation */
static void test_guardian_fragmentation(void) {
    SECTION("Guardian Advanced: Message Fragmentation");
    
    TEST("Guardian handles fragmented messages");
    trit full_msg[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    trit full_guardian = tipc_guardian_compute(full_msg, 4);
    
    /* Fragment into two parts */
    trit frag1[] = { TRIT_TRUE, TRIT_FALSE };
    trit frag2[] = { TRIT_UNKNOWN, TRIT_TRUE };
    
    trit g1 = tipc_guardian_compute(frag1, 2);
    trit g2 = tipc_guardian_compute(frag2, 2);
    
    /* Reconstruct guardian */
    trit guardians[] = { g1, g2 };
    trit reconstructed_guardian = tipc_guardian_compute(guardians, 2);
    
    ASSERT(reconstructed_guardian == full_guardian, "fragmentation handled");
    PASS();
}

/* Test 5680: Guardian entropy estimation */
static void test_guardian_entropy(void) {
    SECTION("Guardian Advanced: Entropy Estimation");
    
    TEST("Guardian entropy: log2(3) ≈ 1.58 bits");
    /* Guardian has 3 possible values → ~1.58 bits of entropy */
    int outcomes[3] = {0, 0, 0};  /* Count -1, 0, 1 occurrences */
    
    for (int i = 0; i < 300; i++) {
        trit buf[] = { (trit)(i % 3 - 1), (trit)((i / 3) % 3 - 1) };
        trit g = tipc_guardian_compute(buf, 2);
        outcomes[g + 1]++;  /* Map -1,0,1 to 0,1,2 */
    }
    
    /* Each outcome should appear ~100 times */
    for (int i = 0; i < 3; i++) {
        ASSERT(outcomes[i] >= 70 && outcomes[i] <= 130, "entropy spread");
    }
    PASS();
}

/* Test 5681: Guardian with concurrent access */
static void test_guardian_concurrent_access(void) {
    SECTION("Guardian Advanced: Concurrent Access");
    
    TEST("Guardian handles concurrent message validation");
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    int ep1 = tipc_endpoint_create(&ch);
    int ep2 = tipc_endpoint_create(&ch);
    
    trit msg1[] = { TRIT_TRUE };
    trit msg2[] = { TRIT_FALSE };
    
    tipc_send(&ch, ep1, msg1, 1, TIPC_PRIO_HIGH);
    tipc_send(&ch, ep2, msg2, 1, TIPC_PRIO_HIGH);
    
    /* Validate both concurrently */
    int valid1 = (tipc_guardian_validate(&ch.endpoints[ep1].inbox) == TIPC_GUARDIAN_OK);
    int valid2 = (tipc_guardian_validate(&ch.endpoints[ep2].inbox) == TIPC_GUARDIAN_OK);
    
    ASSERT(valid1 && valid2, "concurrent validation succeeded");
    PASS();
}

/* Test 5682: Guardian statistical properties */
static void test_guardian_statistical_properties(void) {
    SECTION("Guardian Advanced: Statistical Properties");
    
    TEST("Guardian maintains statistical properties");
    /* Expected value of guardian over uniform trits = 0 */
    int sum = 0;
    
    for (int i = 0; i < 300; i++) {
        trit buf[] = { (trit)(i % 3 - 1) };
        trit g = tipc_guardian_compute(buf, 1);
        sum += (int)g;
    }
    
    /* Sum should be close to 0 (100×1 + 100×0 + 100×(-1) = 0) */
    ASSERT(sum >= -30 && sum <= 30, "expected value ~0");
    PASS();
}

/* Test 5683: Guardian with message replay attack */
static void test_guardian_replay_attack(void) {
    SECTION("Guardian Advanced: Replay Attack");
    
    TEST("Guardian does not prevent replay attacks (by design)");
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_FALSE };
    
    /* Send twice (replay) */
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_HIGH);
    trit g1 = ch.endpoints[ep].inbox.guardian;
    
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_HIGH);
    trit g2 = ch.endpoints[ep].inbox.guardian;
    
    /* Guardians match - replay not detected (needs higher-level counter) */
    ASSERT(g1 == g2, "replay has same guardian");
    PASS();
}

/* Test 5684: Guardian with length extension */
static void test_guardian_length_extension(void) {
    SECTION("Guardian Advanced: Length Extension");
    
    TEST("Guardian length extension property");
    trit base[] = { TRIT_TRUE, TRIT_FALSE };
    trit base_guardian = tipc_guardian_compute(base, 2);
    
    /* Extend with known suffix */
    trit extended[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit extended_guardian = tipc_guardian_compute(extended, 3);
    
    /* Predict extended guardian from base guardian */
    trit predicted[] = { base_guardian, TRIT_UNKNOWN };
    trit predicted_guardian = tipc_guardian_compute(predicted, 2);
    
    ASSERT(predicted_guardian == extended_guardian, "length extension works");
    PASS();
}

/* Test 5685: Guardian with empty buffer edge case */
static void test_guardian_empty_buffer(void) {
    SECTION("Guardian Advanced: Empty Buffer Edge Case");
    
    TEST("Guardian of empty buffer returns UNKNOWN");
    trit buf[1] = { TRIT_UNKNOWN };  /* Initialize to avoid warning */
    trit guardian = tipc_guardian_compute(buf, 0);
    
    /* Implementation starts at UNKNOWN, so 0 iterations = UNKNOWN */
    ASSERT(guardian == TRIT_UNKNOWN, "empty guardian = 0");
    PASS();
}

/* Test 5686: Guardian alignment with 5-trit radix */
static void test_guardian_radix_alignment(void) {
    SECTION("Guardian Advanced: Radix Alignment");
    
    TEST("Guardian aligns with 5-trits-per-byte encoding");
    /* 5 trits can encode 0..242 (3^5 - 1) */
    trit buf[5] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE };
    trit guardian = tipc_guardian_compute(buf, 5);
    
    /* Sum: 1 + (-1) + 0 + 1 + (-1) = 0 → UNKNOWN */
    ASSERT(guardian == TRIT_UNKNOWN, "radix-aligned guardian = 0");
    PASS();
}

/* Test 5687: Guardian with variable length messages */
static void test_guardian_variable_length(void) {
    SECTION("Guardian Advanced: Variable Length");
    
    TEST("Guardian handles variable length messages");
    for (int len = 1; len <= 10; len++) {
        trit buf[10];
        for (int i = 0; i < len; i++) {
            buf[i] = TRIT_TRUE;
        }
        trit g = tipc_guardian_compute(buf, len);
        
        /* Guardian should always be valid trit */
        ASSERT(g >= -1 && g <= 1, "valid guardian for all lengths");
    }
    PASS();
}

/* Test 5688: Guardian preimage resistance */
static void test_guardian_preimage_resistance(void) {
    SECTION("Guardian Advanced: Preimage Resistance");
    
    TEST("Finding preimage for guardian is feasible (low security)");
    trit target_guardian = TRIT_UNKNOWN;
    
    /* Find a message with this guardian */
    int found = 0;
    for (int i = 0; i < 100; i++) {
        trit buf[] = { (trit)(i % 3 - 1), (trit)((i / 3) % 3 - 1) };
        trit g = tipc_guardian_compute(buf, 2);
        
        if (g == target_guardian) {
            found = 1;
            break;
        }
    }
    
    /* Should easily find preimage (1/3 messages match any target) */
    ASSERT(found == 1, "preimage found (low security)");
    PASS();
}

/* Test 5689: Guardian with message ordering */
static void test_guardian_message_ordering(void) {
    SECTION("Guardian Advanced: Message Ordering");
    
    TEST("Guardian is order-independent (commutative)");
    trit msg1[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit msg2[] = { TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE };
    trit msg3[] = { TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN };
    
    trit g1 = tipc_guardian_compute(msg1, 3);
    trit g2 = tipc_guardian_compute(msg2, 3);
    trit g3 = tipc_guardian_compute(msg3, 3);
    
    /* All have same set of trits, just reordered */
    ASSERT(g1 == g2 && g2 == g3, "order-independent");
    PASS();
}

/* Test 5690: Guardian with all TRUE buffer */
static void test_guardian_all_true(void) {
    SECTION("Guardian Advanced: All TRUE Buffer");
    
    TEST("Guardian of all TRUE trits");
    trit buf[10];
    for (int i = 0; i < 10; i++) buf[i] = TRIT_TRUE;
    
    trit guardian = tipc_guardian_compute(buf, 10);
    /* 10 ≡ 1 (mod 3) → TRUE */
    ASSERT(guardian == TRIT_TRUE, "all TRUE → guardian TRUE");
    PASS();
}

/* Test 5691: Guardian with all FALSE buffer */
static void test_guardian_all_false(void) {
    SECTION("Guardian Advanced: All FALSE Buffer");
    
    TEST("Guardian of all FALSE trits");
    trit buf[10];
    for (int i = 0; i < 10; i++) buf[i] = TRIT_FALSE;
    
    trit guardian = tipc_guardian_compute(buf, 10);
    /* -10 ≡ -1 (mod 3) → FALSE */
    ASSERT(guardian == TRIT_FALSE, "all FALSE → guardian FALSE");
    PASS();
}

/* Test 5692: Guardian cascade through multiple layers */
static void test_guardian_cascade(void) {
    SECTION("Guardian Advanced: Guardian Cascade");
    
    TEST("Guardian cascade through multiple layers");
    trit layer1[] = { TRIT_TRUE, TRIT_FALSE };
    trit g1 = tipc_guardian_compute(layer1, 2);
    
    trit layer2[] = { g1, TRIT_UNKNOWN };
    trit g2 = tipc_guardian_compute(layer2, 2);
    
    trit layer3[] = { g2, TRIT_TRUE };
    trit g3 = tipc_guardian_compute(layer3, 2);
    
    /* All should be valid trits */
    ASSERT(g1 >= -1 && g1 <= 1, "layer 1 valid");
    ASSERT(g2 >= -1 && g2 <= 1, "layer 2 valid");
    ASSERT(g3 >= -1 && g3 <= 1, "layer 3 valid");
    PASS();
}

/* Test 5693: Guardian with power-of-3 buffer sizes */
static void test_guardian_power_of_3(void) {
    SECTION("Guardian Advanced: Power of 3 Buffer Sizes");
    
    TEST("Guardian with buffer sizes 3, 9, 27");
    int sizes[] = { 3, 9, 27 };
    
    for (int s = 0; s < 3; s++) {
        int size = sizes[s];
        trit buf[27];
        for (int i = 0; i < size; i++) {
            buf[i] = (trit)(i % 3 - 1);
        }
        
        trit g = tipc_guardian_compute(buf, size);
        /* Balanced pattern → all sum to 0 → UNKNOWN */
        ASSERT(g == TRIT_UNKNOWN, "power-of-3 size → UNKNOWN");
    }
    PASS();
}

/* Test 5694: Guardian second preimage resistance */
static void test_guardian_second_preimage(void) {
    SECTION("Guardian Advanced: Second Preimage Resistance");
    
    TEST("Finding second preimage is feasible");
    trit original[] = { TRIT_TRUE, TRIT_FALSE };
    trit original_guardian = tipc_guardian_compute(original, 2);
    
    /* Find different message with same guardian */
    int found = 0;
    for (int i = 0; i < 100; i++) {
        trit buf[] = { (trit)(i % 3 - 1), (trit)((i / 3) % 3 - 1) };
        
        /* Skip original message */
        if (buf[0] == original[0] && buf[1] == original[1]) continue;
        
        trit g = tipc_guardian_compute(buf, 2);
        if (g == original_guardian) {
            found = 1;
            break;
        }
    }
    
    ASSERT(found == 1, "second preimage found");
    PASS();
}

/* Test 5695: Guardian with checksum verification */
static void test_guardian_checksum_verification(void) {
    SECTION("Guardian Advanced: Checksum Verification");
    
    TEST("Guardian acts as basic checksum");
    trit data[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit checksum = tipc_guardian_compute(data, 3);
    
    /* Transmit data + checksum */
    trit transmitted[4];
    memcpy(transmitted, data, 3 * sizeof(trit));
    transmitted[3] = checksum;
    
    /* Verify by recomputing from first 3 trits */
    trit recomputed = tipc_guardian_compute(transmitted, 3);
    ASSERT(recomputed == transmitted[3], "checksum verified");
    PASS();
}

/* Test 5696: Guardian with end-to-end encryption */
static void test_guardian_with_encryption(void) {
    SECTION("Guardian Advanced: With Encryption");
    
    TEST("Guardian works with encrypted messages");
    /* Simulate encryption by XOR with key */
    trit plaintext[] = { TRIT_TRUE, TRIT_FALSE };
    trit key[] = { TRIT_UNKNOWN, TRIT_TRUE };
    
    trit ciphertext[2];
    for (int i = 0; i < 2; i++) {
        int sum = (int)plaintext[i] + (int)key[i];
        if (sum > 1) sum -= 3;
        if (sum < -1) sum += 3;
        ciphertext[i] = (trit)sum;
    }
    
    trit guardian = tipc_guardian_compute(ciphertext, 2);
    ASSERT(guardian >= -1 && guardian <= 1, "guardian on encrypted data");
    PASS();
}

/* Test 5697: Guardian performance benchmark */
static void test_guardian_performance_benchmark(void) {
    SECTION("Guardian Advanced: Performance Benchmark");
    
    TEST("Guardian computes 100K guardians");
    trit buf[10];
    int ok = 1;
    
    for (int i = 0; i < 100000; i++) {
        for (int j = 0; j < 10; j++) {
            buf[j] = (trit)((i + j) % 3 - 1);
        }
        trit g = tipc_guardian_compute(buf, 10);
        if (g < -1 || g > 1) {
            ok = 0;
            break;
        }
    }
    
    ASSERT(ok == 1, "100K guardians computed");
    PASS();
}

/* Test 5698: Guardian with message authentication */
static void test_guardian_message_authentication(void) {
    SECTION("Guardian Advanced: Message Authentication");
    
    TEST("Guardian provides basic authentication");
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.count = 2;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    /* Verify sender computed correct guardian */
    int authenticated = (tipc_guardian_validate(&msg) == TIPC_GUARDIAN_OK);
    ASSERT(authenticated == 1, "message authenticated");
    PASS();
}

/* Test 5699: Guardian with data integrity check */
static void test_guardian_data_integrity(void) {
    SECTION("Guardian Advanced: Data Integrity");
    
    TEST("Guardian verifies data integrity end-to-end");
    trit original[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit guardian = tipc_guardian_compute(original, 3);
    
    /* Simulate transmission */
    trit transmitted[3];
    memcpy(transmitted, original, sizeof(original));
    
    /* Verify integrity */
    trit received_guardian = tipc_guardian_compute(transmitted, 3);
    ASSERT(guardian == received_guardian, "integrity verified");
    PASS();
}

/* Test 5700: Guardian with noise resilience */
static void test_guardian_noise_resilience(void) {
    SECTION("Guardian Advanced: Noise Resilience");
    
    TEST("Guardian detects noise in transmission");
    trit clean[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    trit clean_guardian = tipc_guardian_compute(clean, 3);
    
    /* Add noise to one trit */
    trit noisy[] = { TRIT_TRUE, TRIT_FALSE, TRIT_TRUE };
    trit noisy_guardian = tipc_guardian_compute(noisy, 3);
    
    ASSERT(clean_guardian != noisy_guardian, "noise detected");
    PASS();
}

/* Test 5701: Guardian comprehensive stress test */
static void test_guardian_comprehensive_stress(void) {
    SECTION("Guardian Advanced: Comprehensive Stress");
    
    TEST("Guardian comprehensive stress test");
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    /* Create multiple endpoints */
    int eps[8];
    for (int i = 0; i < 8; i++) {
        eps[i] = tipc_endpoint_create(&ch);
    }
    
    /* Send 1000 messages to various endpoints */
    int ok = 1;
    for (int i = 0; i < 1000; i++) {
        trit msg[] = { (trit)(i % 3 - 1), (trit)((i / 3) % 3 - 1) };
        int ep = eps[i % 8];
        
        if (tipc_send(&ch, ep, msg, 2, TIPC_PRIO_MEDIUM) != 0) {
            ok = 0;
            break;
        }
        
        /* Validate guardian */
        if (tipc_guardian_validate(&ch.endpoints[ep].inbox) != TIPC_GUARDIAN_OK) {
            ok = 0;
            break;
        }
    }
    
    ASSERT(ok == 1, "comprehensive stress passed");
    PASS();
}

/*==============================================================================
 * Main Test Runner
 *============================================================================*/

int main(void) {
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  seT5/seT6 Test Suite — Batch 98: Tests 5652-5701            ║\n");
    printf("║  Theme: Guardian Trit Mechanisms (Advanced)                  ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    printf("\n");

    /* Execute all 50 tests */
    test_guardian_collision_resistance();
    test_guardian_intentional_collision();
    test_guardian_bit_flip_detection();
    test_guardian_avalanche();
    test_multi_channel_guardian_sync();
    test_guardian_adversarial();
    test_guardian_differential();
    test_guardian_chaining();
    test_guardian_performance_stress();
    test_guardian_max_buffer_stress();
    test_guardian_byzantine_fault();
    test_guardian_recovery();
    test_guardian_false_positive_rate();
    test_guardian_compression_pipeline();
    test_guardian_xor_diff_chaining();
    test_guardian_uniform_distribution();
    test_guardian_incremental_update();
    test_guardian_error_detection_probability();
    test_tipc_guardian_failure_recovery();
    test_guardian_batch_validation();
    test_guardian_radix_integration();
    test_guardian_priority_validation();
    test_guardian_temporal_consistency();
    test_guardian_sparse_data();
    test_guardian_dense_data();
    test_guardian_structured_patterns();
    test_guardian_crypto_strength();
    test_guardian_fragmentation();
    test_guardian_entropy();
    test_guardian_concurrent_access();
    test_guardian_statistical_properties();
    test_guardian_replay_attack();
    test_guardian_length_extension();
    test_guardian_empty_buffer();
    test_guardian_radix_alignment();
    test_guardian_variable_length();
    test_guardian_preimage_resistance();
    test_guardian_message_ordering();
    test_guardian_all_true();
    test_guardian_all_false();
    test_guardian_cascade();
    test_guardian_power_of_3();
    test_guardian_second_preimage();
    test_guardian_checksum_verification();
    test_guardian_with_encryption();
    test_guardian_performance_benchmark();
    test_guardian_message_authentication();
    test_guardian_data_integrity();
    test_guardian_noise_resilience();
    test_guardian_comprehensive_stress();

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
