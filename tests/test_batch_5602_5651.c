/*==============================================================================
 * seT5/seT6 Test Generation — Batch 97
 *
 * Range: Tests 5602-5651 (50 tests)
 * Theme: Guardian Trit Mechanisms
 * Aspect: Guardian checksum computation, validation, tamper detection, radix
 *         purity, T-IPC message integrity, compression with guardian preservation,
 *         differential updates, frequency analysis, balanced ternary mod 3.
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
 * Guardian Trit Mechanism Tests 5602-5651
 *============================================================================*/

/* Test 5602: Guardian computation for simple buffer */
static void test_guardian_simple_buffer(void) {
    SECTION("Guardian Trit: Simple Buffer");
    
    TEST("Guardian of {1,0,-1,1} computes correctly");
    trit buf[] = { TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE };
    trit guardian = tipc_guardian_compute(buf, 4);
    /* Sum: 1 + 0 + (-1) + 1 = 1 (mod 3) → TRUE */
    ASSERT(guardian == TRIT_TRUE, "expected TRUE");
    PASS();
}

/* Test 5603: Guardian of all zeros */
static void test_guardian_all_zeros(void) {
    SECTION("Guardian Trit: All Zeros");
    
    TEST("Guardian of {0,0,0,0} is UNKNOWN");
    trit buf[] = { TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN };
    trit guardian = tipc_guardian_compute(buf, 4);
    ASSERT(guardian == TRIT_UNKNOWN, "expected UNKNOWN");
    PASS();
}

/* Test 5604: Guardian of balanced buffer */
static void test_guardian_balanced(void) {
    SECTION("Guardian Trit: Balanced Buffer");
    
    TEST("Guardian of {1,-1,1,-1,1,-1} is UNKNOWN (balanced)");
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, 
                   TRIT_FALSE, TRIT_TRUE, TRIT_FALSE };
    trit guardian = tipc_guardian_compute(buf, 6);
    ASSERT(guardian == TRIT_UNKNOWN, "expected UNKNOWN");
    PASS();
}

/* Test 5605: Guardian is deterministic */
static void test_guardian_deterministic(void) {
    SECTION("Guardian Trit: Determinism");
    
    TEST("Guardian computation is deterministic");
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit g1 = tipc_guardian_compute(buf, 3);
    trit g2 = tipc_guardian_compute(buf, 3);
    ASSERT(g1 == g2, "expected identical guardians");
    PASS();
}

/* Test 5606: Guardian mod 3 arithmetic */
static void test_guardian_mod3(void) {
    SECTION("Guardian Trit: Mod 3 Arithmetic");
    
    TEST("Guardian uses balanced ternary mod 3 addition");
    trit buf[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    trit guardian = tipc_guardian_compute(buf, 3);
    /* Sum: 1 + 1 + 1 = 3 ≡ 0 (mod 3) → UNKNOWN */
    ASSERT(guardian == TRIT_UNKNOWN, "expected UNKNOWN");
    PASS();
}

/* Test 5607: Guardian with negative sum */
static void test_guardian_negative_sum(void) {
    SECTION("Guardian Trit: Negative Sum");
    
    TEST("Guardian handles negative sums correctly");
    trit buf[] = { TRIT_FALSE, TRIT_FALSE };
    trit guardian = tipc_guardian_compute(buf, 2);
    /* Sum: -1 + (-1) = -2 ≡ 1 (mod 3) → TRUE */
    ASSERT(guardian == TRIT_TRUE, "expected TRUE");
    PASS();
}

/* Test 5608: Guardian validation success */
static void test_guardian_validation_success(void) {
    SECTION("Guardian Trit: Validation Success");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.trits[2] = TRIT_UNKNOWN;
    msg.count = 3;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    TEST("Valid message passes guardian validation");
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_OK, "expected OK");
    PASS();
}

/* Test 5609: Guardian validation failure on tamper */
static void test_guardian_validation_tamper(void) {
    SECTION("Guardian Trit: Validation Tamper Detection");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.count = 2;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    /* Tamper with message */
    msg.trits[0] = TRIT_FALSE;
    
    TEST("Tampered message fails guardian validation");
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_FAIL, "expected FAIL");
    PASS();
}

/* Test 5610: Guardian validation with empty message */
static void test_guardian_validation_empty(void) {
    SECTION("Guardian Trit: Validation Empty Message");
    
    tipc_message_t msg;
    msg.count = 0;
    
    TEST("Empty message fails guardian validation");
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_FAIL, "expected FAIL");
    PASS();
}

/* Test 5611: Guardian validation with NULL pointer */
static void test_guardian_validation_null(void) {
    SECTION("Guardian Trit: Validation NULL Pointer");
    
    TEST("NULL message pointer fails validation");
    ASSERT(tipc_guardian_validate(NULL) == TIPC_GUARDIAN_FAIL, "expected FAIL");
    PASS();
}

/* Test 5612: T-IPC channel initialization */
static void test_tipc_channel_init(void) {
    SECTION("Guardian Trit: T-IPC Channel Init");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    TEST("Channel initialized with zero endpoints");
    ASSERT(ch.active_count == 0, "expected 0");
    
    TEST("Channel statistics zeroed");
    ASSERT(ch.total_sent == 0, "expected 0");
    ASSERT(ch.total_received == 0, "expected 0");
    PASS();
}

/* Test 5613: T-IPC endpoint creation */
static void test_tipc_endpoint_create(void) {
    SECTION("Guardian Trit: T-IPC Endpoint Create");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    TEST("Create first endpoint returns 0");
    int ep = tipc_endpoint_create(&ch);
    ASSERT(ep == 0, "expected 0");
    
    TEST("Active count incremented");
    ASSERT(ch.active_count == 1, "expected 1");
    PASS();
}

/* Test 5614: T-IPC multiple endpoints */
static void test_tipc_multiple_endpoints(void) {
    SECTION("Guardian Trit: T-IPC Multiple Endpoints");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    int ep0 = tipc_endpoint_create(&ch);
    int ep1 = tipc_endpoint_create(&ch);
    int ep2 = tipc_endpoint_create(&ch);
    
    TEST("Multiple endpoints created with sequential IDs");
    ASSERT(ep0 == 0, "expected 0");
    ASSERT(ep1 == 1, "expected 1");
    ASSERT(ep2 == 2, "expected 2");
    PASS();
}

/* Test 5615: T-IPC endpoint limit */
static void test_tipc_endpoint_limit(void) {
    SECTION("Guardian Trit: T-IPC Endpoint Limit");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    
    /* Create max endpoints */
    for (int i = 0; i < TIPC_MAX_ENDPOINTS; i++) {
        tipc_endpoint_create(&ch);
    }
    
    TEST("Exceeding max endpoints returns -1");
    int ep = tipc_endpoint_create(&ch);
    ASSERT(ep == -1, "expected -1");
    PASS();
}

/* Test 5616: T-IPC send with guardian computation */
static void test_tipc_send_guardian(void) {
    SECTION("Guardian Trit: T-IPC Send with Guardian");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    
    TEST("Send computes guardian automatically");
    int result = tipc_send(&ch, ep, msg, 3, TIPC_PRIO_MEDIUM);
    ASSERT(result == 0, "expected 0");
    
    trit expected_guardian = tipc_guardian_compute(msg, 3);
    ASSERT(ch.endpoints[ep].inbox.guardian == expected_guardian, "guardian matches");
    PASS();
}

/* Test 5617: T-IPC receive with guardian validation */
static void test_tipc_recv_guardian(void) {
    SECTION("Guardian Trit: T-IPC Receive with Guardian");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_FALSE };
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_HIGH);
    
    TEST("Receive validates guardian");
    trit recv_buf[10];
    int n = tipc_recv(&ch, ep, recv_buf, 10);
    ASSERT(n == 2, "expected 2 trits");
    ASSERT(recv_buf[0] == TRIT_TRUE, "trit 0 correct");
    ASSERT(recv_buf[1] == TRIT_FALSE, "trit 1 correct");
    PASS();
}

/* Test 5618: T-IPC receive with corrupted guardian */
static void test_tipc_recv_corrupted_guardian(void) {
    SECTION("Guardian Trit: T-IPC Receive Corrupted Guardian");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_TRUE };
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_LOW);
    
    /* Corrupt guardian (correct guardian is TRIT_FALSE, corrupt to TRIT_UNKNOWN) */
    ch.endpoints[ep].inbox.guardian = TRIT_UNKNOWN;
    
    TEST("Receive fails with corrupted guardian and guard_fails incremented");
    trit recv_buf[10];
    int n = tipc_recv(&ch, ep, recv_buf, 10);
    ASSERT(n == -1, "expected -1");
    ASSERT(ch.endpoints[ep].guard_fails > 0, "expected > 0");
    PASS();
}

/* Test 5619: Guardian recomputation after XOR diff */
static void test_guardian_xor_diff(void) {
    SECTION("Guardian Trit: Guardian After XOR Diff");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.trits[2] = TRIT_UNKNOWN;
    msg.count = 3;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    trit delta[] = { TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE };
    
    TEST("XOR diff recomputes guardian");
    int result = tipc_xor_diff(&msg, delta, 3);
    ASSERT(result == 0, "expected 0");
    
    trit expected_guardian = tipc_guardian_compute(msg.trits, msg.count);
    ASSERT(msg.guardian == expected_guardian, "guardian updated");
    PASS();
}

/* Test 5620: Guardian with single trit */
static void test_guardian_single_trit(void) {
    SECTION("Guardian Trit: Single Trit");
    
    TEST("Guardian of single trit is that trit");
    trit buf1[] = { TRIT_TRUE };
    ASSERT(tipc_guardian_compute(buf1, 1) == TRIT_TRUE, "expected TRUE");
    
    trit buf2[] = { TRIT_FALSE };
    ASSERT(tipc_guardian_compute(buf2, 1) == TRIT_FALSE, "expected FALSE");
    
    trit buf3[] = { TRIT_UNKNOWN };
    ASSERT(tipc_guardian_compute(buf3, 1) == TRIT_UNKNOWN, "expected UNKNOWN");
    PASS();
}

/* Test 5621: Guardian commutative property */
static void test_guardian_commutative(void) {
    SECTION("Guardian Trit: Commutative Property");
    
    TEST("Guardian is commutative (order-independent)");
    trit buf1[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    trit buf2[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    
    trit g1 = tipc_guardian_compute(buf1, 3);
    trit g2 = tipc_guardian_compute(buf2, 3);
    ASSERT(g1 == g2, "guardians equal");
    PASS();
}

/* Test 5622: Guardian associative property */
static void test_guardian_associative(void) {
    SECTION("Guardian Trit: Associative Property");
    
    TEST("Guardian is associative");
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    
    /* Compute in parts: (a+b)+(c+d) vs (a+b+c)+d */
    trit g_full = tipc_guardian_compute(buf, 4);
    
    trit g_part1 = tipc_guardian_compute(buf, 2);
    trit g_part2 = tipc_guardian_compute(buf + 2, 2);
    trit combined[] = { g_part1, g_part2 };
    trit g_reassembled = tipc_guardian_compute(combined, 2);
    
    ASSERT(g_full == g_reassembled, "associativity holds");
    PASS();
}

/* Test 5623: Radix guard valid ternary */
static void test_radix_guard_valid(void) {
    SECTION("Guardian Trit: Radix Guard Valid");
    
    TEST("Radix guard accepts valid ternary bytes (< 243)");
    uint8_t data[] = { 0, 121, 242 };  /* All valid: 0 ≤ x < 243 */
    ASSERT(tipc_radix_guard(data, 3) == 0, "expected valid");
    PASS();
}

/* Test 5624: Radix guard binary violation */
static void test_radix_guard_violation(void) {
    SECTION("Guardian Trit: Radix Guard Violation");
    
    TEST("Radix guard detects binary violation (≥ 243)");
    uint8_t data[] = { 100, 243, 50 };  /* 243 is invalid */
    ASSERT(tipc_radix_guard(data, 3) == 1, "expected violation");
    PASS();
}

/* Test 5625: Radix guard boundary */
static void test_radix_guard_boundary(void) {
    SECTION("Guardian Trit: Radix Guard Boundary");
    
    TEST("Radix guard at boundary: 242 valid, 243 invalid");
    uint8_t valid[] = { 242 };
    ASSERT(tipc_radix_guard(valid, 1) == 0, "242 valid");
    
    uint8_t invalid[] = { 243 };
    ASSERT(tipc_radix_guard(invalid, 1) == 1, "243 invalid");
    PASS();
}

/* Test 5626: Radix guard with NULL pointer */
static void test_radix_guard_null(void) {
    SECTION("Guardian Trit: Radix Guard NULL");
    
    TEST("Radix guard with NULL pointer returns violation");
    ASSERT(tipc_radix_guard(NULL, 10) == 1, "expected violation");
    PASS();
}

/* Test 5627: Radix guard with zero length */
static void test_radix_guard_zero_length(void) {
    SECTION("Guardian Trit: Radix Guard Zero Length");
    
    TEST("Radix guard with zero length returns violation");
    uint8_t data[] = { 100 };
    ASSERT(tipc_radix_guard(data, 0) == 1, "expected violation");
    PASS();
}

/* Test 5628: Frequency count all zeros */
static void test_frequency_all_zeros(void) {
    SECTION("Guardian Trit: Frequency All Zeros");
    
    trit buf[] = { TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN };
    tipc_freq_t freq = tipc_frequency(buf, 3);
    
    TEST("Frequency count: all zeros");
    ASSERT(freq.freq_zero == 3, "expected 3 zeros");
    ASSERT(freq.freq_pos == 0, "expected 0 positive");
    ASSERT(freq.freq_neg == 0, "expected 0 negative");
    PASS();
}

/* Test 5629: Frequency count mixed buffer */
static void test_frequency_mixed(void) {
    SECTION("Guardian Trit: Frequency Mixed");
    
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE };
    tipc_freq_t freq = tipc_frequency(buf, 5);
    
    TEST("Frequency count: mixed buffer");
    ASSERT(freq.freq_pos == 2, "expected 2 positive");
    ASSERT(freq.freq_neg == 2, "expected 2 negative");
    ASSERT(freq.freq_zero == 1, "expected 1 zero");
    PASS();
}

/* Test 5630: Compression with guardian preservation */
static void test_compression_guardian_preservation(void) {
    SECTION("Guardian Trit: Compression Guardian Preservation");
    
    trit buf[] = { TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE };
    trit guardian = tipc_guardian_compute(buf, 3);
    
    /* Compress */
    tipc_compressed_t comp;
    int bits = tipc_compress(&comp, buf, 3);
    ASSERT(bits > 0, "compression succeeded");
    
    /* Decompress */
    trit decompressed[10];
    int n = tipc_decompress(decompressed, 10, &comp);
    ASSERT(n == 3, "decompressed 3 trits");
    
    /* Verify guardian preserved */
    trit guardian_after = tipc_guardian_compute(decompressed, n);
    
    TEST("Guardian preserved through compression/decompression");
    ASSERT(guardian == guardian_after, "guardians match");
    PASS();
}

/* Test 5631: Guardian of large buffer */
static void test_guardian_large_buffer(void) {
    SECTION("Guardian Trit: Large Buffer");
    
    trit buf[100];
    for (int i = 0; i < 100; i++) {
        buf[i] = (i % 3 == 0) ? TRIT_TRUE : 
                 (i % 3 == 1) ? TRIT_FALSE : TRIT_UNKNOWN;
    }
    
    TEST("Guardian handles large buffer");
    trit guardian = tipc_guardian_compute(buf, 100);
    /* 34 TRUE + 33 FALSE + 33 UNKNOWN → sum = 34 - 33 + 0 = 1 → TRUE */
    ASSERT(guardian == TRIT_TRUE, "expected TRUE");
    PASS();
}

/* Test 5632: Guardian stability across multiple computations */
static void test_guardian_stability(void) {
    SECTION("Guardian Trit: Stability");
    
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    
    TEST("Guardian stable across 1000 computations");
    trit first = tipc_guardian_compute(buf, 4);
    int ok = 1;
    for (int i = 0; i < 1000; i++) {
        if (tipc_guardian_compute(buf, 4) != first) {
            ok = 0;
            break;
        }
    }
    ASSERT(ok == 1, "guardian stable");
    PASS();
}

/* Test 5633: Guardian with alternating pattern */
static void test_guardian_alternating(void) {
    SECTION("Guardian Trit: Alternating Pattern");
    
    TEST("Guardian of alternating {1,-1,1,-1} pattern");
    trit buf[20];
    for (int i = 0; i < 20; i++) {
        buf[i] = (i % 2 == 0) ? TRIT_TRUE : TRIT_FALSE;
    }
    
    trit guardian = tipc_guardian_compute(buf, 20);
    /* 10 TRUE + 10 FALSE = 0 → UNKNOWN */
    ASSERT(guardian == TRIT_UNKNOWN, "expected UNKNOWN");
    PASS();
}

/* Test 5634: Guardian identity element */
static void test_guardian_identity(void) {
    SECTION("Guardian Trit: Identity Element");
    
    TEST("Guardian identity: adding UNKNOWN (0) preserves value");
    trit buf1[] = { TRIT_TRUE };
    trit buf2[] = { TRIT_TRUE, TRIT_UNKNOWN };
    
    trit g1 = tipc_guardian_compute(buf1, 1);
    trit g2 = tipc_guardian_compute(buf2, 2);
    ASSERT(g1 == g2, "UNKNOWN is identity");
    PASS();
}

/* Test 5635: T-IPC send/receive cycle */
static void test_tipc_send_receive_cycle(void) {
    SECTION("Guardian Trit: T-IPC Send/Receive Cycle");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit original[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    tipc_send(&ch, ep, original, 3, TIPC_PRIO_HIGH);
    
    trit received[10];
    int n = tipc_recv(&ch, ep, received, 10);
    
    TEST("Send/receive cycle preserves data");
    ASSERT(n == 3, "received 3 trits");
    for (int i = 0; i < 3; i++) {
        ASSERT(received[i] == original[i], "trit matches");
    }
    PASS();
}

/* Test 5636: T-IPC statistics tracking */
static void test_tipc_statistics(void) {
    SECTION("Guardian Trit: T-IPC Statistics");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE, TRIT_FALSE };
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_MEDIUM);
    tipc_send(&ch, ep, msg, 2, TIPC_PRIO_MEDIUM);
    
    TEST("Statistics tracked correctly");
    ASSERT(ch.total_sent == 2, "sent count = 2");
    ASSERT(ch.total_raw_trits == 4, "total trits = 4");
    PASS();
}

/* Test 5637: T-IPC priority handling */
static void test_tipc_priority(void) {
    SECTION("Guardian Trit: T-IPC Priority");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE };
    
    TEST("Priority stored in message");
    tipc_send(&ch, ep, msg, 1, TIPC_PRIO_HIGH);
    ASSERT(ch.endpoints[ep].inbox.priority == TIPC_PRIO_HIGH, "priority = HIGH");
    PASS();
}

/* Test 5638: Guardian with max length buffer */
static void test_guardian_max_buffer(void) {
    SECTION("Guardian Trit: Max Length Buffer");
    
    trit buf[TIPC_MAX_TRITS];
    for (int i = 0; i < TIPC_MAX_TRITS; i++) {
        buf[i] = TRIT_UNKNOWN;
    }
    
    TEST("Guardian handles max length buffer");
    trit guardian = tipc_guardian_compute(buf, TIPC_MAX_TRITS);
    ASSERT(guardian == TRIT_UNKNOWN, "expected UNKNOWN");
    PASS();
}

/* Test 5639: Compression ratio calculation */
static void test_compression_ratio(void) {
    SECTION("Guardian Trit: Compression Ratio");
    
    /* Sparse data (many zeros) compresses well */
    trit buf[10];
    for (int i = 0; i < 10; i++) buf[i] = TRIT_UNKNOWN;
    
    tipc_compressed_t comp;
    tipc_compress(&comp, buf, 10);
    
    TEST("Compression ratio calculated");
    int ratio = tipc_compression_ratio(&comp);
    ASSERT(ratio > 0, "expected positive ratio");
    /* 10 trits × 1 bit/trit = 10 bits, vs raw 10 × 1.585 = 15.85 bits
     * ratio = (10 × 1000) / 15.85 ≈ 630 */
    ASSERT(ratio < 1000, "compressed ratio < 1000");
    PASS();
}

/* Test 5640: Compression of uniform distribution */
static void test_compression_uniform(void) {
    SECTION("Guardian Trit: Compression Uniform");
    
    trit buf[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN };
    tipc_compressed_t comp;
    int bits = tipc_compress(&comp, buf, 3);
    
    TEST("Uniform distribution: 1 + 2 + 2 = 5 bits");
    ASSERT(bits == 5, "expected 5 bits");
    PASS();
}

/* Test 5641: Decompression accuracy */
static void test_decompression_accuracy(void) {
    SECTION("Guardian Trit: Decompression Accuracy");
    
    trit original[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    tipc_compressed_t comp;
    tipc_compress(&comp, original, 4);
    
    trit decompressed[10];
    int n = tipc_decompress(decompressed, 10, &comp);
    
    TEST("Decompression restores original data");
    ASSERT(n == 4, "decompressed 4 trits");
    for (int i = 0; i < 4; i++) {
        ASSERT(decompressed[i] == original[i], "trit matches");
    }
    PASS();
}

/* Test 5642: XOR diff with partial delta */
static void test_xor_diff_partial(void) {
    SECTION("Guardian Trit: XOR Diff Partial");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_FALSE;
    msg.trits[2] = TRIT_UNKNOWN;
    msg.count = 3;
    
    /* Apply delta to first 2 trits only */
    trit delta[] = { TRIT_FALSE, TRIT_TRUE };
    tipc_xor_diff(&msg, delta, 2);
    
    TEST("XOR diff applies to partial buffer");
    /* TRUE + FALSE = TRUE - 1 = 0 (mod 3) → UNKNOWN */
    ASSERT(msg.trits[0] == TRIT_UNKNOWN, "trit 0 updated");
    /* FALSE + TRUE = -1 + 1 = 0 → UNKNOWN */
    ASSERT(msg.trits[1] == TRIT_UNKNOWN, "trit 1 updated");
    /* Trit 2 unchanged */
    ASSERT(msg.trits[2] == TRIT_UNKNOWN, "trit 2 unchanged");
    PASS();
}

/* Test 5643: T-IPC endpoint message counter */
static void test_tipc_endpoint_counter(void) {
    SECTION("Guardian Trit: T-IPC Endpoint Counter");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE };
    tipc_send(&ch, ep, msg, 1, TIPC_PRIO_LOW);
    tipc_send(&ch, ep, msg, 1, TIPC_PRIO_LOW);
    tipc_send(&ch, ep, msg, 1, TIPC_PRIO_LOW);
    
    TEST("Endpoint message counter tracks sends");
    ASSERT(ch.endpoints[ep].msg_count == 3, "expected 3");
    PASS();
}

/* Test 5644: Guardian with mixed mod 3 sums */
static void test_guardian_mixed_mod3(void) {
    SECTION("Guardian Trit: Mixed Mod 3 Sums");
    
    TEST("Sum = 4 ≡ 1 (mod 3) → TRUE");
    trit buf1[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    ASSERT(tipc_guardian_compute(buf1, 4) == TRIT_TRUE, "4 mod 3 = 1");
    
    TEST("Sum = 5 ≡ 2 (mod 3) → FALSE (as -1)");
    trit buf2[] = { TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE };
    ASSERT(tipc_guardian_compute(buf2, 5) == TRIT_FALSE, "5 mod 3 = 2 → -1");
    PASS();
}

/* Test 5645: Compression bit count accuracy */
static void test_compression_bit_count(void) {
    SECTION("Guardian Trit: Compression Bit Count");
    
    trit buf[] = { TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE };
    tipc_compressed_t comp;
    int bits = tipc_compress(&comp, buf, 3);
    
    TEST("Compression bit count: 0→1bit, +1→2bits, -1→2bits = 5 total");
    ASSERT(bits == 5, "expected 5 bits");
    ASSERT(comp.bit_count == 5, "comp.bit_count = 5");
    PASS();
}

/* Test 5646: Compression byte count */
static void test_compression_byte_count(void) {
    SECTION("Guardian Trit: Compression Byte Count");
    
    trit buf[10];
    for (int i = 0; i < 10; i++) buf[i] = TRIT_UNKNOWN;
    /* 10 × 1 bit = 10 bits → 2 bytes */
    
    tipc_compressed_t comp;
    tipc_compress(&comp, buf, 10);
    
    TEST("Compression byte count: 10 bits = 2 bytes");
    ASSERT(comp.byte_count == 2, "expected 2 bytes");
    PASS();
}

/* Test 5647: Guardian closure under mod 3 */
static void test_guardian_closure(void) {
    SECTION("Guardian Trit: Closure Under Mod 3");
    
    TEST("Guardian always produces valid trit {-1, 0, 1}");
    int ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit buf[] = { (trit)a, (trit)b };
            trit g = tipc_guardian_compute(buf, 2);
            if (g < -1 || g > 1) {
                ok = 0;
                break;
            }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "guardian closed");
    PASS();
}

/* Test 5648: T-IPC receive clears inbox */
static void test_tipc_receive_clears_inbox(void) {
    SECTION("Guardian Trit: T-IPC Receive Clears Inbox");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit msg[] = { TRIT_TRUE };
    tipc_send(&ch, ep, msg, 1, TIPC_PRIO_LOW);
    
    trit recv_buf[10];
    tipc_recv(&ch, ep, recv_buf, 10);
    
    TEST("Inbox cleared after receive");
    ASSERT(ch.endpoints[ep].inbox.count == 0, "inbox empty");
    PASS();
}

/* Test 5649: T-IPC receive from empty inbox */
static void test_tipc_receive_empty(void) {
    SECTION("Guardian Trit: T-IPC Receive Empty Inbox");
    
    tipc_channel_t ch;
    tipc_channel_init(&ch);
    int ep = tipc_endpoint_create(&ch);
    
    trit recv_buf[10];
    int n = tipc_recv(&ch, ep, recv_buf, 10);
    
    TEST("Receive from empty inbox returns -1");
    ASSERT(n == -1, "expected -1");
    PASS();
}

/* Test 5650: Guardian tamper detection sensitivity */
static void test_guardian_tamper_sensitivity(void) {
    SECTION("Guardian Trit: Tamper Sensitivity");
    
    tipc_message_t msg;
    msg.trits[0] = TRIT_TRUE;
    msg.trits[1] = TRIT_TRUE;
    msg.trits[2] = TRIT_TRUE;
    msg.count = 3;
    msg.guardian = tipc_guardian_compute(msg.trits, msg.count);
    
    /* Single bit flip */
    msg.trits[1] = TRIT_FALSE;
    
    TEST("Single trit change detected by guardian");
    ASSERT(tipc_guardian_validate(&msg) == TIPC_GUARDIAN_FAIL, "tamper detected");
    PASS();
}

/* Test 5651: Frequency analysis for compression estimation */
static void test_frequency_compression_estimate(void) {
    SECTION("Guardian Trit: Frequency Compression Estimate");
    
    /* High frequency of zeros → better compression */
    trit buf1[10];
    for (int i = 0; i < 10; i++) buf1[i] = TRIT_UNKNOWN;
    tipc_freq_t freq1 = tipc_frequency(buf1, 10);
    
    /* Mixed distribution → worse compression */
    trit buf2[] = { TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE };
    tipc_freq_t freq2 = tipc_frequency(buf2, 5);
    
    TEST("Frequency predicts compression efficiency");
    /* More zeros → better compression */
    ASSERT(freq1.freq_zero == 10, "buf1: all zeros");
    ASSERT(freq2.freq_zero == 1, "buf2: 1 zero");
    PASS();
}

/*==============================================================================
 * Main Test Runner
 *============================================================================*/

int main(void) {
    printf("\n");
    printf("╔════════════════════════════════════════════════════════════════╗\n");
    printf("║  seT5/seT6 Test Suite — Batch 97: Tests 5602-5651            ║\n");
    printf("║  Theme: Guardian Trit Mechanisms                              ║\n");
    printf("╚════════════════════════════════════════════════════════════════╝\n");
    printf("\n");

    /* Execute all 50 tests */
    test_guardian_simple_buffer();
    test_guardian_all_zeros();
    test_guardian_balanced();
    test_guardian_deterministic();
    test_guardian_mod3();
    test_guardian_negative_sum();
    test_guardian_validation_success();
    test_guardian_validation_tamper();
    test_guardian_validation_empty();
    test_guardian_validation_null();
    test_tipc_channel_init();
    test_tipc_endpoint_create();
    test_tipc_multiple_endpoints();
    test_tipc_endpoint_limit();
    test_tipc_send_guardian();
    test_tipc_recv_guardian();
    test_tipc_recv_corrupted_guardian();
    test_guardian_xor_diff();
    test_guardian_single_trit();
    test_guardian_commutative();
    test_guardian_associative();
    test_radix_guard_valid();
    test_radix_guard_violation();
    test_radix_guard_boundary();
    test_radix_guard_null();
    test_radix_guard_zero_length();
    test_frequency_all_zeros();
    test_frequency_mixed();
    test_compression_guardian_preservation();
    test_guardian_large_buffer();
    test_guardian_stability();
    test_guardian_alternating();
    test_guardian_identity();
    test_tipc_send_receive_cycle();
    test_tipc_statistics();
    test_tipc_priority();
    test_guardian_max_buffer();
    test_compression_ratio();
    test_compression_uniform();
    test_decompression_accuracy();
    test_xor_diff_partial();
    test_tipc_endpoint_counter();
    test_guardian_mixed_mod3();
    test_compression_bit_count();
    test_compression_byte_count();
    test_guardian_closure();
    test_tipc_receive_clears_inbox();
    test_tipc_receive_empty();
    test_guardian_tamper_sensitivity();
    test_frequency_compression_estimate();

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
