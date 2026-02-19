/**
 * @file test_fault_tolerant_network.c
 * @brief Test suite for seT6 Fault-Tolerant Networking Stack
 *
 * Tests ternary Hamming ECC, multi-radix routing, Byzantine consensus,
 * packet encode/decode, and fault-tolerant NIC operations.
 */

#include "set5/trit.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── Types matching fault_tolerant_network.c exactly ── */

#define TERNARY_HAMMING_N 7
#define TERNARY_HAMMING_K 4
#define TERNARY_HAMMING_PARITY 3
#define MAX_RADIX 6
#define ROUTING_TABLE_SIZE 64
#define MAX_NODES 8
#define CONSENSUS_ROUNDS 3
#define TERNARY_PROTOCOL_VERSION 1
#define MAX_PAYLOAD_TRITS 64

typedef struct {
    trit radix;
    trit routing_table[ROUTING_TABLE_SIZE];
    trit distance_vector[ROUTING_TABLE_SIZE];
    trit neighbor_state[8];
} multi_radix_router_t;

typedef struct {
    trit node_id;
    trit proposal;
    trit votes[MAX_NODES];
    trit decided_value;
    trit consensus_state;  /* UNKNOWN=ongoing, TRUE=decided, FALSE=failed */
} consensus_instance_t;

typedef struct {
    trit version;
    trit source_addr;
    trit dest_addr;
    trit packet_type;
    trit sequence_num;
    trit payload[MAX_PAYLOAD_TRITS];
    trit checksum;
    trit error_correction[7];
} ternary_packet_t;

typedef struct {
    multi_radix_router_t router;
    consensus_instance_t consensus;
    ternary_packet_t     send_buffer[8];
    ternary_packet_t     recv_buffer[8];
    trit                 fault_status;
    trit                 redundancy_level;
} fault_tolerant_nic_t;

extern void ternary_hamming_encode(const trit data[4], trit codeword[7]);
extern int  ternary_hamming_decode(trit codeword[7], trit data[4]);
extern void multi_radix_route(multi_radix_router_t *router, trit dest_addr,
                               trit *next_hop, trit *path_cost);
extern void ternary_consensus(consensus_instance_t *instance, trit node_proposal);
extern void ternary_packet_encode(ternary_packet_t *packet);
extern int  ternary_packet_decode(ternary_packet_t *packet);
extern int  ft_nic_send(fault_tolerant_nic_t *nic, ternary_packet_t *packet);
extern int  ft_nic_receive(fault_tolerant_nic_t *nic, ternary_packet_t *packet);

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
 * Ternary Hamming ECC Tests
 * ════════════════════════════════════════════════════════════ */

void test_hamming_encode_basic(void) {
    TEST(hamming_encode_basic);
    trit data[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit codeword[7];

    ternary_hamming_encode(data, codeword);

    /* Systematic code: first 4 positions are data */
    ASSERT_EQ(codeword[0], TRIT_TRUE,    "data[0] at pos 0");
    ASSERT_EQ(codeword[1], TRIT_FALSE,   "data[1] at pos 1");
    ASSERT_EQ(codeword[2], TRIT_UNKNOWN, "data[2] at pos 2");
    ASSERT_EQ(codeword[3], TRIT_TRUE,    "data[3] at pos 3");
    /* Remaining parities must be valid trits */
    for (int i = 4; i < 7; i++) {
        ASSERT_TRUE(codeword[i] >= TRIT_FALSE && codeword[i] <= TRIT_TRUE,
                     "parity trit valid");
    }
    PASS();
}

void test_hamming_roundtrip(void) {
    TEST(hamming_encode_decode_roundtrip);
    trit data[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    trit codeword[7];
    trit decoded[4];

    ternary_hamming_encode(data, codeword);
    int result = ternary_hamming_decode(codeword, decoded);

    ASSERT_EQ(result, 0, "no error detected");
    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(decoded[i], data[i], "decoded matches original");
    }
    PASS();
}

void test_hamming_single_error_correction(void) {
    TEST(hamming_single_error_correction);
    trit data[4] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE};
    trit codeword[7];

    ternary_hamming_encode(data, codeword);

    /* Inject error at position 2: flip to different value */
    if (codeword[2] == TRIT_TRUE)
        codeword[2] = TRIT_FALSE;
    else
        codeword[2] = TRIT_TRUE;

    trit decoded[4];
    ternary_hamming_decode(codeword, decoded);

    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(decoded[i], data[i], "corrected data matches original");
    }
    PASS();
}

void test_hamming_all_zero(void) {
    TEST(hamming_all_zero_data);
    trit data[4] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
    trit codeword[7];
    trit decoded[4];

    ternary_hamming_encode(data, codeword);
    int result = ternary_hamming_decode(codeword, decoded);

    ASSERT_EQ(result, 0, "zero data no error");
    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(decoded[i], TRIT_UNKNOWN, "zero roundtrip");
    }
    PASS();
}

void test_hamming_all_positive(void) {
    TEST(hamming_all_positive_data);
    trit data[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit codeword[7];
    trit decoded[4];

    ternary_hamming_encode(data, codeword);
    int result = ternary_hamming_decode(codeword, decoded);

    ASSERT_EQ(result, 0, "all-positive no error");
    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(decoded[i], TRIT_TRUE, "positive roundtrip");
    }
    PASS();
}

void test_hamming_all_negative(void) {
    TEST(hamming_all_negative_data);
    trit data[4] = {TRIT_FALSE, TRIT_FALSE, TRIT_FALSE, TRIT_FALSE};
    trit codeword[7];
    trit decoded[4];

    ternary_hamming_encode(data, codeword);
    int result = ternary_hamming_decode(codeword, decoded);

    ASSERT_EQ(result, 0, "all-negative no error");
    for (int i = 0; i < 4; i++) {
        ASSERT_EQ(decoded[i], TRIT_FALSE, "negative roundtrip");
    }
    PASS();
}

void test_hamming_error_each_position(void) {
    TEST(hamming_error_at_every_position);
    trit data[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit codeword_orig[7];
    ternary_hamming_encode(data, codeword_orig);

    for (int pos = 0; pos < 7; pos++) {
        trit codeword[7];
        memcpy(codeword, codeword_orig, sizeof(codeword));

        /* Inject +1 error */
        if (codeword[pos] == TRIT_TRUE)
            codeword[pos] = TRIT_FALSE;
        else
            codeword[pos] = TRIT_TRUE;

        trit decoded[4];
        ternary_hamming_decode(codeword, decoded);

        for (int i = 0; i < 4; i++) {
            if (decoded[i] != data[i]) {
                FAIL("error correction failed at some position");
                return;
            }
        }
    }
    PASS();
}

void test_hamming_all_81_patterns(void) {
    TEST(hamming_all_81_data_patterns);
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    int all_ok = 1;

    for (int a = 0; a < 3 && all_ok; a++) {
        for (int b = 0; b < 3 && all_ok; b++) {
            for (int c = 0; c < 3 && all_ok; c++) {
                for (int d = 0; d < 3 && all_ok; d++) {
                    trit data[4] = {vals[a], vals[b], vals[c], vals[d]};
                    trit codeword[7], decoded[4];

                    ternary_hamming_encode(data, codeword);
                    int r = ternary_hamming_decode(codeword, decoded);

                    if (r != 0) { all_ok = 0; break; }
                    for (int i = 0; i < 4; i++) {
                        if (decoded[i] != data[i]) { all_ok = 0; break; }
                    }
                }
            }
        }
    }
    ASSERT_TRUE(all_ok, "all 81 patterns roundtrip");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Multi-Radix Routing Tests
 * ════════════════════════════════════════════════════════════ */

void test_routing_basic(void) {
    TEST(multi_radix_route_basic);
    multi_radix_router_t router;
    memset(&router, 0, sizeof(router));
    router.radix = TRIT_TRUE;
    router.routing_table[0] = TRIT_TRUE;
    router.distance_vector[0] = TRIT_UNKNOWN;   /* cost = 0 */

    trit next_hop, cost;
    multi_radix_route(&router, TRIT_TRUE, &next_hop, &cost);

    /* Entry 0 has cost 0, which is < initial min_cost (1) */
    ASSERT_EQ(next_hop, TRIT_TRUE, "next_hop from table");
    ASSERT_EQ(cost, TRIT_UNKNOWN, "cost = 0");
    PASS();
}

void test_routing_empty(void) {
    TEST(multi_radix_route_empty_table);
    multi_radix_router_t router;
    memset(&router, 0, sizeof(router));
    router.radix = TRIT_TRUE;

    trit next_hop, cost;
    multi_radix_route(&router, TRIT_TRUE, &next_hop, &cost);

    /* All entries UNKNOWN → no valid route found */
    ASSERT_EQ(next_hop, TRIT_UNKNOWN, "empty → no hop");
    ASSERT_EQ(cost, TRIT_TRUE, "empty → max cost");
    PASS();
}

void test_routing_multiple(void) {
    TEST(multi_radix_route_selects_lowest_cost);
    multi_radix_router_t router;
    memset(&router, 0, sizeof(router));
    router.radix = TRIT_TRUE;

    /* Entry 0: hop=TRUE, cost=FALSE (= -1, lowest) */
    router.routing_table[0] = TRIT_TRUE;
    router.distance_vector[0] = TRIT_FALSE;

    /* Entry 1: hop=FALSE, cost=TRUE (= 1, higher) */
    router.routing_table[1] = TRIT_FALSE;
    router.distance_vector[1] = TRIT_TRUE;

    trit next_hop, cost;
    multi_radix_route(&router, TRIT_TRUE, &next_hop, &cost);

    /* cost(-1) < cost(1), so entry 0 wins */
    ASSERT_EQ(next_hop, TRIT_TRUE, "lowest cost hop");
    ASSERT_EQ(cost, TRIT_FALSE, "cost = -1");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Byzantine Consensus Tests
 * ════════════════════════════════════════════════════════════ */

void test_consensus_unanimous(void) {
    TEST(consensus_unanimous_agreement);
    consensus_instance_t inst;
    memset(&inst, 0, sizeof(inst));
    for (int i = 0; i < MAX_NODES; i++)
        inst.votes[i] = TRIT_TRUE;

    ternary_consensus(&inst, TRIT_TRUE);

    /* 8/8 TRUE >= threshold 5 → decided TRUE */
    ASSERT_EQ(inst.decided_value, TRIT_TRUE, "unanimous TRUE");
    ASSERT_EQ(inst.consensus_state, TRIT_TRUE, "state=decided");
    PASS();
}

void test_consensus_majority(void) {
    TEST(consensus_2_of_3_majority);
    consensus_instance_t inst;
    memset(&inst, 0, sizeof(inst));
    for (int i = 0; i < 6; i++) inst.votes[i] = TRIT_TRUE;
    inst.votes[6] = TRIT_FALSE;
    inst.votes[7] = TRIT_FALSE;

    ternary_consensus(&inst, TRIT_TRUE);

    /* 6 TRUE >= 5 → decided TRUE */
    ASSERT_EQ(inst.decided_value, TRIT_TRUE, "majority TRUE");
    ASSERT_EQ(inst.consensus_state, TRIT_TRUE, "state=decided");
    PASS();
}

void test_consensus_no_majority(void) {
    TEST(consensus_no_majority_ongoing);
    consensus_instance_t inst;
    memset(&inst, 0, sizeof(inst));
    inst.votes[0] = inst.votes[1] = inst.votes[2] = TRIT_TRUE;
    inst.votes[3] = inst.votes[4] = inst.votes[5] = TRIT_FALSE;
    inst.votes[6] = inst.votes[7] = TRIT_UNKNOWN;

    ternary_consensus(&inst, TRIT_TRUE);

    /* 3 TRUE, 3 FALSE, 2 UNKNOWN — none >= 5 */
    ASSERT_EQ(inst.consensus_state, TRIT_UNKNOWN, "no majority → ongoing");
    PASS();
}

void test_consensus_false_majority(void) {
    TEST(consensus_false_majority_decides);
    consensus_instance_t inst;
    memset(&inst, 0, sizeof(inst));
    for (int i = 0; i < 6; i++) inst.votes[i] = TRIT_FALSE;
    inst.votes[6] = TRIT_TRUE;
    inst.votes[7] = TRIT_TRUE;

    ternary_consensus(&inst, TRIT_FALSE);

    /* 6 FALSE >= 5 → decided FALSE */
    ASSERT_EQ(inst.decided_value, TRIT_FALSE, "false majority");
    ASSERT_EQ(inst.consensus_state, TRIT_TRUE, "state=decided");
    PASS();
}

void test_consensus_unknown_majority(void) {
    TEST(consensus_unknown_supermajority);
    consensus_instance_t inst;
    memset(&inst, 0, sizeof(inst));
    /* 6 UNKNOWN (from memset), 2 FALSE */
    inst.votes[6] = TRIT_FALSE;
    inst.votes[7] = TRIT_FALSE;
    /* votes[0..5] = 0 = UNKNOWN via memset */

    ternary_consensus(&inst, TRIT_UNKNOWN);

    /* 6 UNKNOWN >= 5 → decided UNKNOWN */
    ASSERT_EQ(inst.decided_value, TRIT_UNKNOWN, "unknown majority");
    ASSERT_EQ(inst.consensus_state, TRIT_TRUE, "state=decided");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Packet Encode/Decode Tests
 * ════════════════════════════════════════════════════════════ */

void test_packet_encode_decode(void) {
    TEST(packet_encode_decode_roundtrip);
    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_TRUE;
    pkt.dest_addr   = TRIT_FALSE;
    pkt.packet_type = TRIT_UNKNOWN;
    pkt.payload[0]  = TRIT_TRUE;
    pkt.payload[1]  = TRIT_FALSE;

    ternary_packet_encode(&pkt);
    int result = ternary_packet_decode(&pkt);

    /* 0 = no error */
    ASSERT_EQ(result, 0, "decode no error");
    PASS();
}

void test_packet_tamper(void) {
    TEST(packet_checksum_tamper_detection);
    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_FALSE;
    pkt.dest_addr   = TRIT_TRUE;
    pkt.payload[0]  = TRIT_TRUE;
    pkt.payload[1]  = TRIT_FALSE;

    ternary_packet_encode(&pkt);
    /* Tamper with payload */
    pkt.payload[0] = TRIT_UNKNOWN;

    int result = ternary_packet_decode(&pkt);
    ASSERT_EQ(result, -1, "tamper detected");
    PASS();
}

void test_packet_zero_payload(void) {
    TEST(packet_zero_payload);
    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_TRUE;
    pkt.dest_addr   = TRIT_TRUE;
    /* All payload = 0 via memset */

    ternary_packet_encode(&pkt);
    int result = ternary_packet_decode(&pkt);
    ASSERT_EQ(result, 0, "zero payload ok");
    PASS();
}

void test_packet_full_payload(void) {
    TEST(packet_full_payload);
    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version   = TRIT_TRUE;
    pkt.source_addr = TRIT_TRUE;
    pkt.dest_addr = TRIT_FALSE;
    for (int i = 0; i < MAX_PAYLOAD_TRITS; i++) {
        pkt.payload[i] = (i % 3 == 0) ? TRIT_TRUE
                       : (i % 3 == 1) ? TRIT_FALSE
                       : TRIT_UNKNOWN;
    }

    ternary_packet_encode(&pkt);
    int result = ternary_packet_decode(&pkt);
    ASSERT_EQ(result, 0, "full payload ok");
    PASS();
}

void test_packet_header_preserved(void) {
    TEST(packet_header_preserved_through_ecc);
    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_FALSE;
    pkt.dest_addr   = TRIT_TRUE;
    pkt.packet_type = TRIT_FALSE;

    ternary_packet_encode(&pkt);
    ternary_packet_decode(&pkt);

    /* Decode overwrites header from ECC — should match original */
    ASSERT_EQ(pkt.version,     TRIT_TRUE,  "version preserved");
    ASSERT_EQ(pkt.source_addr, TRIT_FALSE, "src preserved");
    ASSERT_EQ(pkt.dest_addr,   TRIT_TRUE,  "dest preserved");
    ASSERT_EQ(pkt.packet_type, TRIT_FALSE, "type preserved");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Fault-Tolerant NIC Tests
 * ════════════════════════════════════════════════════════════ */

void test_ftnic_send(void) {
    TEST(ftnic_send_packet);
    fault_tolerant_nic_t nic;
    memset(&nic, 0, sizeof(nic));
    nic.router.radix = TRIT_TRUE;
    nic.router.routing_table[0] = TRIT_TRUE;

    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_FALSE;
    pkt.dest_addr   = TRIT_TRUE;
    pkt.payload[0]  = TRIT_TRUE;

    int result = ft_nic_send(&nic, &pkt);
    ASSERT_EQ(result, 0, "send success");
    PASS();
}

void test_ftnic_receive(void) {
    TEST(ftnic_receive_valid);
    fault_tolerant_nic_t nic;
    memset(&nic, 0, sizeof(nic));

    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_TRUE;
    pkt.dest_addr   = TRIT_FALSE;
    pkt.payload[0]  = TRIT_TRUE;

    ternary_packet_encode(&pkt);
    int result = ft_nic_receive(&nic, &pkt);
    ASSERT_EQ(result, 0, "receive success");
    PASS();
}

void test_ftnic_receive_corrupted(void) {
    TEST(ftnic_receive_corrupted_packet);
    fault_tolerant_nic_t nic;
    memset(&nic, 0, sizeof(nic));

    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_TRUE;
    pkt.dest_addr   = TRIT_FALSE;
    pkt.payload[0]  = TRIT_TRUE;
    pkt.payload[1]  = TRIT_FALSE;

    ternary_packet_encode(&pkt);
    /* Corrupt payload → checksum mismatch */
    pkt.payload[0] = TRIT_UNKNOWN;

    int result = ft_nic_receive(&nic, &pkt);
    ASSERT_EQ(result, -1, "corrupted detected");
    PASS();
}

void test_ftnic_fault_tracking(void) {
    TEST(ftnic_fault_status_tracking);
    fault_tolerant_nic_t nic;
    memset(&nic, 0, sizeof(nic));

    ternary_packet_t pkt;
    memset(&pkt, 0, sizeof(pkt));
    pkt.version     = TRIT_TRUE;
    pkt.source_addr = TRIT_TRUE;
    pkt.dest_addr   = TRIT_FALSE;

    ternary_packet_encode(&pkt);
    ft_nic_receive(&nic, &pkt);

    /* Clean receive → fault_status remains UNKNOWN */
    ASSERT_EQ(nic.fault_status, TRIT_UNKNOWN, "no faults after clean recv");
    PASS();
}

/* ── Main ── */

int main(void) {
    printf("=== Fault-Tolerant Networking Test Suite ===\n\n");

    printf("[Ternary Hamming ECC]\n");
    test_hamming_encode_basic();
    test_hamming_roundtrip();
    test_hamming_single_error_correction();
    test_hamming_all_zero();
    test_hamming_all_positive();
    test_hamming_all_negative();
    test_hamming_error_each_position();
    test_hamming_all_81_patterns();

    printf("\n[Multi-Radix Routing]\n");
    test_routing_basic();
    test_routing_empty();
    test_routing_multiple();

    printf("\n[Byzantine Consensus]\n");
    test_consensus_unanimous();
    test_consensus_majority();
    test_consensus_no_majority();
    test_consensus_false_majority();
    test_consensus_unknown_majority();

    printf("\n[Packet Encode/Decode]\n");
    test_packet_encode_decode();
    test_packet_tamper();
    test_packet_zero_payload();
    test_packet_full_payload();
    test_packet_header_preserved();

    printf("\n[Fault-Tolerant NIC]\n");
    test_ftnic_send();
    test_ftnic_receive();
    test_ftnic_receive_corrupted();
    test_ftnic_fault_tracking();

    printf("\n=== Results: %d passed, %d failed ===\n", tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
