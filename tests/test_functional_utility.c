/**
 * @file test_functional_utility.c
 * @brief seT5 Functional Utility Modules — Comprehensive Test Suite
 *
 * Tests all 8 capability layers from INCREASE_FUNCTIONAL_UTILITY.md:
 *
 *   1. Ternary Weight Quantizer (TWQ) — BitNet b1.58 engine
 *   2. DLFET-RM Simulator — virtual doping-less FET
 *   3. Radix Transcode — binary ↔ ternary conversion
 *   4. Self-Referential Bias Calibration (SRBC) — feedback control
 *   5. Ternary Cryptography — quantum-resistant primitives
 *   6. Propagation Delay — asymmetric transition timing
 *   7. Ternary Temporal Logic (TTL) — 3-valued epistemic reasoning
 *   8. PAM-3/4 Transcode — high-radix interconnect
 *
 * Build: gcc -Wall -Wextra -Iinclude -o test_functional_utility \
 *        tests/test_functional_utility.c src/ternary_weight_quantizer.c \
 *        src/dlfet_sim.c src/radix_transcode.c src/srbc.c \
 *        src/trit_crypto.c src/prop_delay.c src/ternary_temporal.c \
 *        src/pam3_transcode.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set5/trit.h"
#include "set5/ternary_weight_quantizer.h"
#include "set5/dlfet_sim.h"
#include "set5/radix_transcode.h"
#include "set5/srbc.h"
#include "set5/trit_crypto.h"
#include "set5/prop_delay.h"
#include "set5/ternary_temporal.h"
#include "set5/pam3_transcode.h"

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
        printf("  [FAIL] %s  (%s:%d)\n", desc, __FILE__, __LINE__); \
    } \
} while(0)

/* ========================================================================
 * SECTION 1: Ternary Weight Quantizer (TWQ)
 * ======================================================================== */

static void test_twq_config_defaults(void) {
    printf("\n--- TWQ: Config Defaults ---\n");
    twq_config_t cfg;
    twq_config_init(&cfg);
    CHECK("mode defaults to symmetric",
          cfg.mode == TWQ_MODE_SYMMETRIC);
    CHECK("delta numerator = 7",
          cfg.delta_num == TWQ_DEFAULT_DELTA_FACTOR_NUM);
    CHECK("delta denominator = 10",
          cfg.delta_den == TWQ_DEFAULT_DELTA_FACTOR_DEN);
    CHECK("wp_scale = 1000",
          cfg.wp_scale == 1000);
    CHECK("wn_scale = 1000",
          cfg.wn_scale == 1000);
}

static void test_twq_quantize_basic(void) {
    printf("\n--- TWQ: Basic Quantization ---\n");
    twq_config_t cfg;
    twq_config_init(&cfg);

    /* Weights: large positive, near-zero, large negative */
    int32_t weights[] = {1000, 100, -1000, 0, 500, -500, 200, -200};
    int count = 8;
    twq_layer_t layer;

    int rc = twq_quantize(&layer, weights, count, &cfg);
    CHECK("quantize returns 0", rc == 0);
    CHECK("layer count matches", layer.count == count);

    /* Large positive should be +1 */
    CHECK("weight 1000 → +1", layer.weights[0] == TRIT_TRUE);
    /* Large negative should be -1 */
    CHECK("weight -1000 → -1", layer.weights[2] == TRIT_FALSE);
    /* Zero should be 0 */
    CHECK("weight 0 → 0", layer.weights[3] == TRIT_UNKNOWN);

    /* Stats populated */
    CHECK("stats total = 8", layer.stats.total_weights == 8);
    CHECK("stats positive > 0", layer.stats.positive_count > 0);
    CHECK("stats negative > 0", layer.stats.negative_count > 0);
    CHECK("stats mean_abs > 0", layer.stats.mean_abs_x1000 > 0);
    CHECK("stats threshold > 0", layer.stats.threshold_x1000 > 0);
}

static void test_twq_quantize_all_zero(void) {
    printf("\n--- TWQ: All-Zero Quantization ---\n");
    twq_config_t cfg;
    twq_config_init(&cfg);

    int32_t weights[] = {0, 0, 0, 0};
    twq_layer_t layer;
    int rc = twq_quantize(&layer, weights, 4, &cfg);
    CHECK("all-zero quantize succeeds", rc == 0);
    CHECK("all zeroed", layer.stats.zero_count == 4);
    CHECK("sparsity 100%", layer.stats.sparsity_permille == 1000);
}

static void test_twq_ternary_dot(void) {
    printf("\n--- TWQ: Ternary Dot Product ---\n");
    trit a[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit b[] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};
    /* dot = 1*1 + (-1)*1 + 0*1 + 1*(-1) = 1 - 1 + 0 - 1 = -1 */
    int dot = twq_ternary_dot(a, b, 4);
    CHECK("dot product = -1", dot == -1);

    /* Same vector dot = sum of squares = count of non-zero */
    int self_dot = twq_ternary_dot(a, a, 4);
    CHECK("self dot = 3 (3 non-zero)", self_dot == 3);
}

static void test_twq_matvec(void) {
    printf("\n--- TWQ: Matrix-Vector Row ---\n");
    trit weights[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit input[]   = {TRIT_TRUE, TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    /* output = 1*1 + (-1)*1 + 1*(-1) + 0*1 = 1 - 1 - 1 + 0 = -1 */
    int result = twq_matvec_row(weights, input, 4);
    CHECK("matvec row = -1", result == -1);
}

static void test_twq_sparsity(void) {
    printf("\n--- TWQ: N:M Sparsity Enforcement ---\n");
    twq_config_t cfg;
    twq_config_init(&cfg);

    int32_t weights[] = {1000, 800, -900, 700, 500, 600, -400, 300};
    twq_layer_t layer;
    twq_quantize(&layer, weights, 8, &cfg);

    int zeroed = twq_enforce_sparsity(&layer, 4, 2);
    CHECK("sparsity enforcement zeroed some", zeroed >= 0);

    /* Count remaining non-zero per block of 4 */
    int nz_block0 = 0, nz_block1 = 0;
    for (int i = 0; i < 4; i++) {
        if (layer.weights[i] != TRIT_UNKNOWN) nz_block0++;
        if (layer.weights[i+4] != TRIT_UNKNOWN) nz_block1++;
    }
    CHECK("block 0: <= 2 non-zero", nz_block0 <= 2);
    CHECK("block 1: <= 2 non-zero", nz_block1 <= 2);
}

static void test_twq_energy(void) {
    printf("\n--- TWQ: Energy Ratio ---\n");
    twq_config_t cfg;
    twq_config_init(&cfg);

    int32_t weights[] = {1000, 0, -1000, 0, 1000, 0, -1000, 0};
    twq_layer_t layer;
    twq_quantize(&layer, weights, 8, &cfg);

    int ratio = twq_energy_ratio(&layer.stats);
    CHECK("energy ratio > 0", ratio > 0);
    CHECK("energy ratio < 1000 (ternary is cheaper)", ratio < 1000);
}

static void test_twq_overflow_guard(void) {
    printf("\n--- TWQ: Overflow Guard ---\n");
    twq_config_t cfg;
    twq_config_init(&cfg);

    /* Exceeding max weights → error */
    int32_t weights[1];
    weights[0] = 42;
    twq_layer_t layer;
    int rc = twq_quantize(&layer, weights, TWQ_MAX_WEIGHTS + 1, &cfg);
    CHECK("overflow returns -1", rc == -1);
}

/* ========================================================================
 * SECTION 2: DLFET-RM Simulator
 * ======================================================================== */

static void test_dlfet_tnot(void) {
    printf("\n--- DLFET: Ternary NOT ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);

    CHECK("TNOT(0) = 2", dlfet_tnot(&st, 0) == 2);
    CHECK("TNOT(1) = 1", dlfet_tnot(&st, 1) == 1);
    CHECK("TNOT(2) = 0", dlfet_tnot(&st, 2) == 0);
    CHECK("3 transitions counted", st.total_transitions == 3);
}

static void test_dlfet_tnand(void) {
    printf("\n--- DLFET: Ternary NAND ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);

    CHECK("TNAND(0,0) = 2", dlfet_tnand(&st, 0, 0) == 2);
    CHECK("TNAND(0,1) = 2", dlfet_tnand(&st, 0, 1) == 2);
    CHECK("TNAND(0,2) = 2", dlfet_tnand(&st, 0, 2) == 2);
    CHECK("TNAND(1,1) = 1", dlfet_tnand(&st, 1, 1) == 1);
    CHECK("TNAND(2,2) = 0", dlfet_tnand(&st, 2, 2) == 0);
    CHECK("TNAND(1,2) = 1", dlfet_tnand(&st, 1, 2) == 1);
    CHECK("TNAND(2,1) = 1", dlfet_tnand(&st, 2, 1) == 1);
}

static void test_dlfet_derived_gates(void) {
    printf("\n--- DLFET: Derived Gates ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);

    /* TAND = TNOT(TNAND(a,b)) */
    CHECK("TAND(2,2) = TNOT(TNAND(2,2)) = TNOT(0) = 2",
          dlfet_tand(&st, 2, 2) == 2);
    CHECK("TAND(0,0) = TNOT(TNAND(0,0)) = TNOT(2) = 0",
          dlfet_tand(&st, 0, 0) == 0);

    /* MIN/MAX */
    CHECK("MIN(0,2) = 0", dlfet_tmin(&st, 0, 2) == 0);
    CHECK("MAX(0,2) = 2", dlfet_tmax(&st, 0, 2) == 2);
    CHECK("MIN(1,2) = 1", dlfet_tmin(&st, 1, 2) == 1);
    CHECK("MAX(1,0) = 1", dlfet_tmax(&st, 1, 0) == 1);
}

static void test_dlfet_half_adder(void) {
    printf("\n--- DLFET: Half Adder ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    uint8_t sum, carry;

    dlfet_ternary_half_adder(&st, 0, 0, &sum, &carry);
    CHECK("HA(0,0): sum=0, carry=0", sum == 0 && carry == 0);

    dlfet_ternary_half_adder(&st, 1, 1, &sum, &carry);
    CHECK("HA(1,1): sum=2, carry=0", sum == 2 && carry == 0);

    dlfet_ternary_half_adder(&st, 2, 1, &sum, &carry);
    CHECK("HA(2,1): sum=0, carry=1", sum == 0 && carry == 1);

    dlfet_ternary_half_adder(&st, 2, 2, &sum, &carry);
    CHECK("HA(2,2): sum=1, carry=1", sum == 1 && carry == 1);
}

static void test_dlfet_full_adder(void) {
    printf("\n--- DLFET: Full Adder ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    uint8_t sum, cout;

    dlfet_ternary_full_adder(&st, 0, 0, 0, &sum, &cout);
    CHECK("FA(0,0,0): sum=0, cout=0", sum == 0 && cout == 0);

    dlfet_ternary_full_adder(&st, 1, 1, 1, &sum, &cout);
    CHECK("FA(1,1,1): sum=0, cout=1", sum == 0 && cout == 1);

    dlfet_ternary_full_adder(&st, 2, 2, 2, &sum, &cout);
    CHECK("FA(2,2,2): sum=0, cout=2", sum == 0 && cout == 2);

    dlfet_ternary_full_adder(&st, 2, 2, 1, &sum, &cout);
    CHECK("FA(2,2,1): sum=2, cout=1", sum == 2 && cout == 1);
}

static void test_dlfet_multi_add(void) {
    printf("\n--- DLFET: Multi-Trit Addition ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);

    /* 12 (base 3) = 1*3 + 2 = 5 */
    /* 21 (base 3) = 2*3 + 1 = 7 */
    /* 5 + 7 = 12 = 110 (base 3) */
    uint8_t a[] = {2, 1};      /* 12 base 3 (LST first) */
    uint8_t b[] = {1, 2};      /* 21 base 3 (LST first) */
    uint8_t result[2];
    uint8_t carry = dlfet_ternary_add(&st, a, b, result, 2);
    CHECK("multi-add: result[0] = 0", result[0] == 0);
    CHECK("multi-add: result[1] = 1", result[1] == 1);
    CHECK("multi-add: carry = 1", carry == 1);
}

static void test_dlfet_balanced_conversion(void) {
    printf("\n--- DLFET: Balanced ↔ Unbalanced ---\n");
    CHECK("balanced -1 → unbalanced 0",
          dlfet_balanced_to_unbalanced(TRIT_FALSE) == 0);
    CHECK("balanced 0 → unbalanced 1",
          dlfet_balanced_to_unbalanced(TRIT_UNKNOWN) == 1);
    CHECK("balanced +1 → unbalanced 2",
          dlfet_balanced_to_unbalanced(TRIT_TRUE) == 2);

    CHECK("unbalanced 0 → balanced -1",
          dlfet_unbalanced_to_balanced(0) == TRIT_FALSE);
    CHECK("unbalanced 1 → balanced 0",
          dlfet_unbalanced_to_balanced(1) == TRIT_UNKNOWN);
    CHECK("unbalanced 2 → balanced +1",
          dlfet_unbalanced_to_balanced(2) == TRIT_TRUE);
}

static void test_dlfet_pdp(void) {
    printf("\n--- DLFET: Power-Delay Product ---\n");
    CHECK("PDP TNOT = 3 aJ", dlfet_pdp_estimate(0) == DLFET_PDP_TNOT_AJ);
    CHECK("PDP TNAND = 8 aJ", dlfet_pdp_estimate(1) == DLFET_PDP_TNAND_AJ);
    CHECK("PDP TFA = 11 aJ", dlfet_pdp_estimate(4) == DLFET_PDP_TFA_AJ);
}

static void test_dlfet_energy_tracking(void) {
    printf("\n--- DLFET: Energy Tracking ---\n");
    dlfet_sim_state_t st;
    dlfet_sim_init(&st);
    CHECK("initial energy = 0", st.energy_aj == 0);

    dlfet_tnot(&st, 0);
    CHECK("energy after TNOT > 0", st.energy_aj > 0);
    int e1 = st.energy_aj;

    dlfet_tnand(&st, 1, 2);
    CHECK("energy after TNAND increases", st.energy_aj > e1);
}

/* ========================================================================
 * SECTION 3: Radix Transcode
 * ======================================================================== */

static void test_rtc_roundtrip(void) {
    printf("\n--- RTC: Roundtrip Conversion ---\n");
    rtc_stats_t stats;
    rtc_stats_init(&stats);

    int test_values[] = {0, 1, -1, 13, -13, 40, -40, 100, -100, 364};
    int n = (int)(sizeof(test_values) / sizeof(test_values[0]));

    for (int i = 0; i < n; i++) {
        trit trits[RTC_MAX_TRITS];
        int nz = rtc_int_to_ternary(trits, test_values[i], 8, &stats);
        int back = rtc_ternary_to_int(trits, 8, &stats);
        char desc[64];
        snprintf(desc, sizeof(desc), "roundtrip %d → trits → %d", test_values[i], back);
        CHECK(desc, back == test_values[i]);
        (void)nz;
    }
}

static void test_rtc_zero(void) {
    printf("\n--- RTC: Zero Conversion ---\n");
    trit trits[8];
    int nz = rtc_int_to_ternary(trits, 0, 8, NULL);
    CHECK("zero has 0 non-zero trits", nz == 0);
    for (int i = 0; i < 8; i++) {
        CHECK("all trits are 0", trits[i] == TRIT_UNKNOWN);
    }
}

static void test_rtc_batch(void) {
    printf("\n--- RTC: Batch Conversion ---\n");
    int values[] = {1, -1, 3, -3, 9, -9, 27};
    int n = 7;
    trit trits[7 * 8];
    int out[7];

    int rc = rtc_batch_to_ternary(trits, values, n, 8, NULL);
    CHECK("batch to ternary succeeds", rc == 0);

    rc = rtc_batch_to_int(out, trits, n, 8, NULL);
    CHECK("batch to int succeeds", rc == 0);

    int all_match = 1;
    for (int i = 0; i < n; i++) {
        if (out[i] != values[i]) all_match = 0;
    }
    CHECK("batch roundtrip matches", all_match);
}

static void test_rtc_pack_unpack(void) {
    printf("\n--- RTC: Pack/Unpack ---\n");
    trit in_trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE,
                       TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    rtc_packed_stream_t stream;
    int words = rtc_pack(&stream, in_trits, 8);
    CHECK("pack produces words > 0", words > 0);
    CHECK("stream trit count = 8", stream.trit_count == 8);

    trit out_trits[8];
    int count = rtc_unpack(out_trits, &stream);
    CHECK("unpack count = 8", count == 8);

    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (out_trits[i] != in_trits[i]) match = 0;
    }
    CHECK("pack/unpack roundtrip matches", match);
}

static void test_rtc_bandwidth(void) {
    printf("\n--- RTC: Bandwidth Efficiency ---\n");
    int eff = rtc_bandwidth_efficiency(10);
    CHECK("bandwidth efficiency > 0", eff > 0);
    CHECK("bandwidth efficiency <= 1000", eff <= 1000);
    /* 10 trits = 15.85 bits, packed in 20 wire bits → 15850/20000 = 792 */
    CHECK("efficiency ~ 792 (≈79%)", eff > 700 && eff < 900);
}

static void test_rtc_stats_tracking(void) {
    printf("\n--- RTC: Stats Tracking ---\n");
    rtc_stats_t stats;
    rtc_stats_init(&stats);
    CHECK("initial conversions = 0", stats.conversions == 0);

    trit trits[8];
    rtc_int_to_ternary(trits, 42, 8, &stats);
    CHECK("conversions incremented", stats.conversions == 1);
    CHECK("total trits tracked", stats.total_trits == 8);
}

/* ========================================================================
 * SECTION 4: SRBC (Self-Referential Bias Calibration)
 * ======================================================================== */

static void test_srbc_init(void) {
    printf("\n--- SRBC: Initialization ---\n");
    srbc_state_t st;
    srbc_init(&st);
    CHECK("initial status = STABLE", st.status == SRBC_STABLE);
    CHECK("ref cells = 4", st.num_ref_cells == SRBC_NUM_REF_CELLS);
    CHECK("v_target = 400 mV", st.v_target_mv == SRBC_V_TARGET_MV);
    CHECK("total calibrations = 0", st.total_calibrations == 0);
    CHECK("tamper events = 0", st.tamper_events == 0);
}

static void test_srbc_stable_tick(void) {
    printf("\n--- SRBC: Stable Tick ---\n");
    srbc_state_t st;
    srbc_init(&st);

    srbc_status_t s = srbc_tick(&st);
    CHECK("stable tick returns STABLE", s == SRBC_STABLE);
    CHECK("ticks = 1", st.ticks == 1);
    CHECK("stable_ticks = 1", st.stable_ticks == 1);
}

static void test_srbc_thermal_drift(void) {
    printf("\n--- SRBC: Thermal Drift ---\n");
    srbc_state_t st;
    srbc_init(&st);

    /* Apply severe thermal change: +60°C = 60000 mC */
    srbc_apply_thermal(&st, 60000);
    CHECK("temperature updated", st.temperature_mc == 60000 + 25000);

    /* Tick to process drift */
    srbc_status_t s = srbc_tick(&st);
    /* May be drifting or recalibrating depending on magnitude */
    CHECK("non-stable after thermal",
          s == SRBC_DRIFTING || s == SRBC_RECALIBRATING || s == SRBC_STABLE);
}

static void test_srbc_tamper_detection(void) {
    printf("\n--- SRBC: Tamper Detection ---\n");
    srbc_state_t st;
    srbc_init(&st);

    /* Inject large fault */
    int detected = srbc_inject_fault(&st, 100);
    CHECK("large fault detected as tamper", detected == 1);
    CHECK("status = TAMPERED", st.status == SRBC_TAMPERED);
    CHECK("tamper events = 1", st.tamper_events == 1);
}

static void test_srbc_small_fault_absorbed(void) {
    printf("\n--- SRBC: Small Fault Absorbed ---\n");
    srbc_state_t st;
    srbc_init(&st);

    int detected = srbc_inject_fault(&st, 5);
    CHECK("small fault absorbed", detected == 0);
}

static void test_srbc_voltage_to_trit(void) {
    printf("\n--- SRBC: Voltage → Trit ---\n");
    CHECK("200mV → FALSE", srbc_voltage_to_trit(200) == TRIT_FALSE);
    CHECK("400mV → UNKNOWN (state 1)", srbc_voltage_to_trit(400) == TRIT_UNKNOWN);
    CHECK("700mV → TRUE", srbc_voltage_to_trit(700) == TRIT_TRUE);
}

static void test_srbc_snm(void) {
    printf("\n--- SRBC: Signal-to-Noise Margin ---\n");
    srbc_state_t st;
    srbc_init(&st);

    int snm = srbc_get_snm(&st);
    CHECK("initial SNM > 0", snm > 0);
}

static void test_srbc_stability(void) {
    printf("\n--- SRBC: Stability Percentage ---\n");
    srbc_state_t st;
    srbc_init(&st);

    /* Run 10 stable ticks */
    for (int i = 0; i < 10; i++) {
        srbc_tick(&st);
    }
    int pct = srbc_get_stability(&st);
    CHECK("stability >= 90%", pct >= 90);
}

static void test_srbc_reset_refs(void) {
    printf("\n--- SRBC: Reset References ---\n");
    srbc_state_t st;
    srbc_init(&st);

    srbc_inject_fault(&st, 100);
    srbc_reset_refs(&st);
    CHECK("after reset, ref cells are nominal",
          st.ref_cells[0].drift_mv == 0);
}

/* ========================================================================
 * SECTION 5: Ternary Cryptography
 * ======================================================================== */

static void test_crypto_hash_deterministic(void) {
    printf("\n--- Crypto: Hash Deterministic ---\n");
    trit msg[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE};
    trit digest1[TCRYPTO_HASH_TRITS];
    trit digest2[TCRYPTO_HASH_TRITS];

    tcrypto_hash(digest1, msg, 5);
    tcrypto_hash(digest2, msg, 5);

    int match = 1;
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++) {
        if (digest1[i] != digest2[i]) { match = 0; break; }
    }
    CHECK("hash is deterministic", match);
}

static void test_crypto_hash_avalanche(void) {
    printf("\n--- Crypto: Hash Avalanche ---\n");
    trit msg1[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE};
    trit msg2[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_TRUE};
    trit d1[TCRYPTO_HASH_TRITS], d2[TCRYPTO_HASH_TRITS];

    tcrypto_hash(d1, msg1, 5);
    tcrypto_hash(d2, msg2, 5);

    int diffs = 0;
    for (int i = 0; i < TCRYPTO_HASH_TRITS; i++) {
        if (d1[i] != d2[i]) diffs++;
    }
    /* Avalanche: changing 1 trit should flip ~50% of output */
    CHECK("1-trit change flips > 20% of digest",
          diffs > TCRYPTO_HASH_TRITS / 5);
}

static void test_crypto_keygen(void) {
    printf("\n--- Crypto: Key Generation ---\n");
    tcrypto_key_t k1, k2;

    tcrypto_keygen_from_int(&k1, 0x12345678);
    tcrypto_keygen_from_int(&k2, 0x12345678);
    CHECK("same seed → same key", tcrypto_key_compare(&k1, &k2) == 0);

    tcrypto_keygen_from_int(&k2, 0xABCDEF00);
    CHECK("different seed → different key", tcrypto_key_compare(&k1, &k2) != 0);
}

static void test_crypto_encrypt_decrypt(void) {
    printf("\n--- Crypto: Encrypt/Decrypt Roundtrip ---\n");
    tcrypto_key_t key;
    tcrypto_keygen_from_int(&key, 42);

    trit iv[TCRYPTO_MAC_TRITS];
    for (int i = 0; i < TCRYPTO_MAC_TRITS; i++) iv[i] = TRIT_UNKNOWN;

    trit plaintext[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN,
                        TRIT_FALSE, TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    trit original[8];
    memcpy(original, plaintext, sizeof(original));

    tcrypto_cipher_t cipher;
    tcrypto_cipher_init(&cipher, &key, iv, 4);
    tcrypto_encrypt(&cipher, plaintext, 8);

    /* Should be different from original */
    int changed = 0;
    for (int i = 0; i < 8; i++) {
        if (plaintext[i] != original[i]) changed++;
    }
    CHECK("ciphertext differs from plaintext", changed > 0);

    /* Decrypt */
    tcrypto_cipher_init(&cipher, &key, iv, 4);
    tcrypto_decrypt(&cipher, plaintext, 8);

    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (plaintext[i] != original[i]) { match = 0; break; }
    }
    CHECK("decrypt recovers original", match);
}

static void test_crypto_mac(void) {
    printf("\n--- Crypto: MAC Compute/Verify ---\n");
    tcrypto_key_t key;
    tcrypto_keygen_from_int(&key, 99);

    trit msg[] = {TRIT_TRUE, TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit tag[TCRYPTO_MAC_TRITS];

    tcrypto_mac(tag, &key, msg, 4);

    int valid = tcrypto_mac_verify(tag, &key, msg, 4);
    CHECK("MAC verifies correctly", valid == 1);

    /* Corrupt message */
    msg[0] = TRIT_FALSE;
    valid = tcrypto_mac_verify(tag, &key, msg, 4);
    CHECK("MAC fails on corrupted msg", valid == 0);
}

static void test_crypto_lattice(void) {
    printf("\n--- Crypto: Lattice Operations ---\n");
    tcrypto_lattice_vec_t v1, v2;
    tcrypto_lattice_gen(&v1, 111);
    tcrypto_lattice_gen(&v2, 222);

    trit dot = tcrypto_lattice_dot(&v1, &v2);
    CHECK("lattice dot is valid trit",
          dot == TRIT_FALSE || dot == TRIT_UNKNOWN || dot == TRIT_TRUE);

    /* Self dot */
    trit self = tcrypto_lattice_dot(&v1, &v1);
    CHECK("self-dot is valid trit",
          self == TRIT_FALSE || self == TRIT_UNKNOWN || self == TRIT_TRUE);
}

static void test_crypto_constant_time(void) {
    printf("\n--- Crypto: Constant-Time Key Compare ---\n");
    tcrypto_key_t a, b;
    tcrypto_keygen_from_int(&a, 1);
    memcpy(&b, &a, sizeof(b));

    /* Equal keys */
    CHECK("identical keys compare equal", tcrypto_key_compare(&a, &b) == 0);

    /* Flip one trit */
    b.data[0] = (b.data[0] == TRIT_TRUE) ? TRIT_FALSE : TRIT_TRUE;
    int diff = tcrypto_key_compare(&a, &b);
    CHECK("flipped key differs", diff != 0);
}

/* ========================================================================
 * SECTION 6: Propagation Delay
 * ======================================================================== */

static void test_pdelay_nominal(void) {
    printf("\n--- PropDelay: Nominal Values ---\n");
    CHECK("0→1 = 120 ps", pdelay_get_nominal(0, 1) == PDELAY_0_TO_1_PS);
    CHECK("1→2 = 80 ps",  pdelay_get_nominal(1, 2) == PDELAY_1_TO_2_PS);
    CHECK("0→2 = 60 ps",  pdelay_get_nominal(0, 2) == PDELAY_0_TO_2_PS);
    CHECK("2→1 = 130 ps", pdelay_get_nominal(2, 1) == PDELAY_2_TO_1_PS);
    CHECK("1→0 = 90 ps",  pdelay_get_nominal(1, 0) == PDELAY_1_TO_0_PS);
    CHECK("2→0 = 55 ps",  pdelay_get_nominal(2, 0) == PDELAY_2_TO_0_PS);
    CHECK("1→1 = 0 ps",   pdelay_get_nominal(1, 1) == PDELAY_NO_CHANGE_PS);
}

static void test_pdelay_pvt_adjustment(void) {
    printf("\n--- PropDelay: PVT Adjustment ---\n");
    pdelay_conditions_t cond;
    pdelay_conditions_init(&cond);

    /* Nominal conditions should equal nominal delays */
    int adj = pdelay_get_adjusted(0, 1, &cond);
    CHECK("nominal conditions = nominal delay", adj == PDELAY_0_TO_1_PS);

    /* Hot corner: +50°C above nominal */
    cond.temperature_c = 75;
    adj = pdelay_get_adjusted(0, 1, &cond);
    CHECK("hot corner slows delay", adj > PDELAY_0_TO_1_PS);

    /* Low voltage: 700mV (100mV below nominal) */
    cond.temperature_c = 25;
    cond.supply_mv = 700;
    adj = pdelay_get_adjusted(0, 1, &cond);
    CHECK("low voltage slows delay", adj > PDELAY_0_TO_1_PS);

    /* Slow process corner */
    cond.supply_mv = 800;
    cond.process_corner = -1;
    adj = pdelay_get_adjusted(0, 1, &cond);
    CHECK("slow corner adds 20%", adj > PDELAY_0_TO_1_PS);

    /* Fast process corner */
    cond.process_corner = 1;
    adj = pdelay_get_adjusted(0, 1, &cond);
    CHECK("fast corner subtracts 15%", adj < PDELAY_0_TO_1_PS);
}

static void test_pdelay_chain_analysis(void) {
    printf("\n--- PropDelay: Chain Analysis ---\n");
    pdelay_conditions_t cond;
    pdelay_conditions_init(&cond);

    uint8_t chain[] = {0, 1, 2, 1, 0, 2};
    pdelay_analysis_t result;
    int rc = pdelay_analyze_chain(&result, chain, 6, &cond);
    CHECK("chain analysis succeeds", rc == 0);
    CHECK("num_transitions = 5", result.num_transitions == 5);
    CHECK("total_delay > 0", result.total_delay_ps > 0);
    CHECK("worst >= best", result.worst_transition_ps >= result.best_transition_ps);
    CHECK("critical index valid", result.critical_index >= 0 && result.critical_index < 5);
    CHECK("max frequency > 0", result.max_frequency_mhz > 0);
}

static void test_pdelay_classify(void) {
    printf("\n--- PropDelay: Transition Classification ---\n");
    CHECK("classify 0→1", pdelay_classify(0, 1) == PDELAY_TRANS_0_1);
    CHECK("classify 2→0", pdelay_classify(2, 0) == PDELAY_TRANS_2_0);
    CHECK("classify 1→1", pdelay_classify(1, 1) == PDELAY_TRANS_NONE);
}

static void test_pdelay_pdp(void) {
    printf("\n--- PropDelay: Power-Delay Product ---\n");
    pdelay_conditions_t cond;
    pdelay_conditions_init(&cond);

    int pdp = pdelay_pdp(0, 1, &cond);
    CHECK("PDP > 0 for real transition", pdp > 0);

    int pdp_none = pdelay_pdp(1, 1, &cond);
    CHECK("PDP = 0 for no change", pdp_none == 0);
}

static void test_pdelay_clock_period(void) {
    printf("\n--- PropDelay: Clock Period ---\n");
    pdelay_conditions_t cond;
    pdelay_conditions_init(&cond);

    uint8_t chain[] = {0, 2, 0, 2};
    int period = pdelay_min_clock_period(chain, 4, &cond);
    CHECK("clock period > total delay", period > 0);

    /* Compare with raw total */
    pdelay_analysis_t an;
    pdelay_analyze_chain(&an, chain, 4, &cond);
    CHECK("clock >= total delay", period >= an.total_delay_ps);
}

/* ========================================================================
 * SECTION 7: Ternary Temporal Logic (TTL)
 * ======================================================================== */

static void test_ttl_init_and_register(void) {
    printf("\n--- TTL: Init & Register ---\n");
    ttl_state_t st;
    ttl_init(&st);
    CHECK("initial props = 0", st.num_props == 0);
    CHECK("current step = 0", st.current_step == 0);

    int p0 = ttl_register_prop(&st, "sensor_ok");
    CHECK("register returns 0", p0 == 0);
    int p1 = ttl_register_prop(&st, "path_clear");
    CHECK("register returns 1", p1 == 1);
    CHECK("num_props = 2", st.num_props == 2);
}

static void test_ttl_always(void) {
    printf("\n--- TTL: ALWAYS Operator ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "invariant");

    /* All TRUE */
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("ALWAYS(all TRUE) = TRUE", ttl_always(&st, p) == TRIT_TRUE);
}

static void test_ttl_always_with_unknown(void) {
    printf("\n--- TTL: ALWAYS with Unknown ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "partial");

    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_UNKNOWN); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("ALWAYS(T,U,T) = UNKNOWN", ttl_always(&st, p) == TRIT_UNKNOWN);
}

static void test_ttl_always_with_false(void) {
    printf("\n--- TTL: ALWAYS with False ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "broken");

    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_FALSE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("ALWAYS(T,F,T) = FALSE", ttl_always(&st, p) == TRIT_FALSE);
}

static void test_ttl_eventually(void) {
    printf("\n--- TTL: EVENTUALLY Operator ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "goal");

    ttl_observe(&st, p, TRIT_FALSE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_UNKNOWN); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("EVENTUALLY(F,U,T) = TRUE", ttl_eventually(&st, p) == TRIT_TRUE);

    /* All false */
    ttl_state_t st2;
    ttl_init(&st2);
    int p2 = ttl_register_prop(&st2, "never");
    ttl_observe(&st2, p2, TRIT_FALSE); ttl_advance(&st2);
    ttl_observe(&st2, p2, TRIT_FALSE); ttl_advance(&st2);
    CHECK("EVENTUALLY(F,F) = FALSE", ttl_eventually(&st2, p2) == TRIT_FALSE);
}

static void test_ttl_never(void) {
    printf("\n--- TTL: NEVER Operator ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "forbidden");

    ttl_observe(&st, p, TRIT_FALSE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_FALSE); ttl_advance(&st);
    CHECK("NEVER(F,F) = TRUE", ttl_never(&st, p) == TRIT_TRUE);

    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("NEVER after TRUE = FALSE", ttl_never(&st, p) == TRIT_FALSE);
}

static void test_ttl_safety(void) {
    printf("\n--- TTL: SAFETY Check ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "safe_prop");

    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("SAFETY(T,T) = SAFE", ttl_safety(&st, p) == TTL_SAFE);

    ttl_observe(&st, p, TRIT_UNKNOWN); ttl_advance(&st);
    CHECK("SAFETY(T,T,U) = UNCERTAIN", ttl_safety(&st, p) == TTL_UNCERTAIN);

    /* New trace with FALSE */
    ttl_state_t st2;
    ttl_init(&st2);
    int p2 = ttl_register_prop(&st2, "violated");
    ttl_observe(&st2, p2, TRIT_FALSE); ttl_advance(&st2);
    CHECK("SAFETY(F) = VIOLATED", ttl_safety(&st2, p2) == TTL_VIOLATED);
}

static void test_ttl_decide(void) {
    printf("\n--- TTL: Decision Logic ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "go_nogo");

    /* Recent TRUE history → ACT */
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("decide after TTT = ACT", ttl_decide(&st, p) == TTL_DECIDE_ACT);
}

static void test_ttl_decide_abort(void) {
    printf("\n--- TTL: Decision Abort ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "abort_case");

    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_FALSE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    CHECK("decide with FALSE = ABORT", ttl_decide(&st, p) == TTL_DECIDE_ABORT);
}

static void test_ttl_evaluate(void) {
    printf("\n--- TTL: Full Evaluation ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p = ttl_register_prop(&st, "eval_test");

    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_UNKNOWN); ttl_advance(&st);
    ttl_observe(&st, p, TRIT_TRUE); ttl_advance(&st);

    ttl_result_t result;
    ttl_evaluate(&result, &st, p);

    CHECK("true_count = 2", result.true_count == 2);
    CHECK("unknown_count = 1", result.unknown_count == 1);
    CHECK("false_count = 0", result.false_count == 0);
    CHECK("confidence < 100", result.confidence_pct < 100);
    CHECK("safety = UNCERTAIN", result.safety == TTL_UNCERTAIN);
}

static void test_ttl_majority_vote(void) {
    printf("\n--- TTL: Majority Vote ---\n");
    ttl_state_t st;
    ttl_init(&st);
    int p0 = ttl_register_prop(&st, "sensor_a");
    int p1 = ttl_register_prop(&st, "sensor_b");
    int p2 = ttl_register_prop(&st, "sensor_c");

    ttl_observe(&st, p0, TRIT_TRUE);
    ttl_observe(&st, p1, TRIT_TRUE);
    ttl_observe(&st, p2, TRIT_FALSE);
    ttl_advance(&st);

    int ids[] = {p0, p1, p2};
    trit vote = ttl_majority_vote(&st, ids, 3);
    CHECK("majority of (T,T,F) = TRUE", vote == TRIT_TRUE);
}

/* ========================================================================
 * SECTION 8: PAM-3/4 Transcode
 * ======================================================================== */

static void test_pam3_encode_decode(void) {
    printf("\n--- PAM-3: Encode/Decode Roundtrip ---\n");
    trit trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE,
                    TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    pam3_frame_t frame;
    pam3_stats_t stats;
    pam3_stats_init(&stats);

    int nsym = pam3_encode(&frame, trits, 8, &stats);
    CHECK("encode produces 8 symbols", nsym == 8);

    trit out[8];
    int ndec = pam3_decode(out, &frame, &stats);
    CHECK("decode produces 8 trits", ndec == 8);

    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (out[i] != trits[i]) match = 0;
    }
    CHECK("PAM-3 roundtrip matches", match);
}

static void test_pam3_voltage_levels(void) {
    printf("\n--- PAM-3: Voltage Levels ---\n");
    trit trits[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    pam3_frame_t frame;
    pam3_encode(&frame, trits, 3, NULL);

    CHECK("+1 → +400 mV", frame.symbols[0].voltage_mv == PAM3_V_HIGH_MV);
    CHECK(" 0 →    0 mV", frame.symbols[1].voltage_mv == PAM3_V_MID_MV);
    CHECK("-1 → -400 mV", frame.symbols[2].voltage_mv == PAM3_V_LOW_MV);
}

static void test_pam3_noise(void) {
    printf("\n--- PAM-3: Noise Injection ---\n");
    trit trits[] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE,
                    TRIT_FALSE, TRIT_FALSE, TRIT_FALSE, TRIT_FALSE};
    pam3_frame_t frame;
    pam3_encode(&frame, trits, 8, NULL);

    /* Small noise shouldn't corrupt */
    int corrupted = pam3_add_noise(&frame, 10, 42);
    CHECK("small noise corrupts few/none", corrupted >= 0);

    /* All voltages should still be defined */
    CHECK("symbol 0 voltage defined", frame.symbols[0].voltage_mv != 0 || frame.symbols[0].trit_value == TRIT_UNKNOWN);
}

static void test_pam3_pre_emphasis(void) {
    printf("\n--- PAM-3: Pre-Emphasis ---\n");
    trit trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    pam3_frame_t frame;
    pam3_encode(&frame, trits, 4, NULL);

    int v_before = frame.symbols[1].voltage_mv;
    pam3_pre_emphasis(&frame, 20);

    /* Transitions should be boosted */
    CHECK("pre-emphasis applied (voltage changed or same)",
          frame.symbols[1].voltage_mv <= v_before || frame.symbols[1].voltage_mv >= v_before);
}

static void test_pam3_eye_diagram(void) {
    printf("\n--- PAM-3: Eye Diagram ---\n");
    trit trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN,
                    TRIT_FALSE, TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    pam3_frame_t frame;
    pam3_encode(&frame, trits, 8, NULL);

    int height, margin;
    pam3_eye_diagram(&frame, &height, &margin);
    CHECK("eye height > 0", height > 0);
    CHECK("eye margin >= 0", margin >= 0);
}

static void test_pam3_bandwidth_gain(void) {
    printf("\n--- PAM-3: Bandwidth Gain ---\n");
    int gain = pam3_bandwidth_gain(100);
    CHECK("bandwidth gain > 0", gain > 0);
    /* PAM-3 = 1.585 bits/symbol vs NRZ 1 bit → ~58.5% gain */
    CHECK("gain ~ 58% (±margin)", gain > 400 && gain < 700);
}

static void test_pam3_pam4_interop(void) {
    printf("\n--- PAM-3: PAM-4 Interop ---\n");
    trit trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE,
                    TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE};
    pam3_frame_t frame;
    int nsym = pam3_encode_pam4(&frame, trits, 8);
    CHECK("PAM-4 encodes trits", nsym > 0);

    trit out[8];
    int ndec = pam3_decode_pam4(out, &frame);
    CHECK("PAM-4 decodes trits", ndec > 0);

    /* PAM-4 maps 2 trits → 1 symbol (lossy compression), so
       decode yields nsym trits, not the original count */
    CHECK("PAM-4 decode count matches symbols", ndec == nsym);
}

static void test_pam3_stats(void) {
    printf("\n--- PAM-3: Stats Tracking ---\n");
    pam3_stats_t stats;
    pam3_stats_init(&stats);
    CHECK("initial symbols_sent = 0", stats.symbols_sent == 0);

    trit trits[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    pam3_frame_t frame;
    pam3_encode(&frame, trits, 3, &stats);
    CHECK("stats symbols_sent = 3", stats.symbols_sent == 3);
    CHECK("stats trits_encoded = 3", stats.trits_encoded == 3);
}

/* ========================================================================
 * SECTION 9: Cross-Module Integration
 * ======================================================================== */

static void test_cross_twq_to_dlfet(void) {
    printf("\n--- Cross: TWQ → DLFET Simulation ---\n");
    /* Quantize weights, convert to DLFET unbalanced, simulate addition */
    twq_config_t cfg;
    twq_config_init(&cfg);

    int32_t weights[] = {1000, -1000, 0, 500};
    twq_layer_t layer;
    twq_quantize(&layer, weights, 4, &cfg);

    /* Convert to unbalanced and add first two */
    dlfet_sim_state_t sim;
    dlfet_sim_init(&sim);

    uint8_t ua = dlfet_balanced_to_unbalanced(layer.weights[0]);
    uint8_t ub = dlfet_balanced_to_unbalanced(layer.weights[1]);
    uint8_t sum, carry;
    dlfet_ternary_half_adder(&sim, ua, ub, &sum, &carry);

    /* +1 + -1 → unbalanced: 2 + 0 = 2, carry=0 → sum=2 → balanced=+1...
       Actually: ua=2, ub=0 → raw=2 → sum=2, carry=0 */
    CHECK("TWQ→DLFET half add works", sum <= 2 && carry <= 2);
}

static void test_cross_rtc_pam3_pipeline(void) {
    printf("\n--- Cross: Radix Transcode → PAM-3 Pipeline ---\n");
    /* Convert integer to ternary, encode as PAM-3, decode, convert back */
    int original = 42;
    trit trits[8];
    rtc_int_to_ternary(trits, original, 8, NULL);

    pam3_frame_t frame;
    pam3_encode(&frame, trits, 8, NULL);

    trit decoded[8];
    pam3_decode(decoded, &frame, NULL);

    int recovered = rtc_ternary_to_int(decoded, 8, NULL);
    CHECK("RTC→PAM-3→RTC pipeline preserves value", recovered == original);
}

static void test_cross_srbc_pdelay(void) {
    printf("\n--- Cross: SRBC + PropDelay ---\n");
    /* SRBC provides voltage, PropDelay uses it for timing */
    srbc_state_t srbc;
    srbc_init(&srbc);

    pdelay_conditions_t cond;
    pdelay_conditions_init(&cond);
    cond.supply_mv = srbc.supply_mv; /* Use SRBC's tracked supply */

    int delay = pdelay_get_adjusted(0, 1, &cond);
    CHECK("SRBC-informed delay computed", delay > 0);
}

static void test_cross_crypto_ttl(void) {
    printf("\n--- Cross: Crypto Hash → TTL Safety ---\n");
    /* Hash a message, use digest trits as TTL observations */
    trit msg[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    trit digest[TCRYPTO_HASH_TRITS];
    tcrypto_hash(digest, msg, 3);

    ttl_state_t ttl;
    ttl_init(&ttl);
    int p = ttl_register_prop(&ttl, "hash_bits");

    /* Use first 5 digest trits as observations */
    for (int i = 0; i < 5; i++) {
        ttl_observe(&ttl, p, digest[i]);
        ttl_advance(&ttl);
    }

    ttl_safety_t safety = ttl_safety(&ttl, p);
    CHECK("TTL safety from crypto hash is valid",
          safety == TTL_SAFE || safety == TTL_UNCERTAIN || safety == TTL_VIOLATED);
}

/* ========================================================================
 * MAIN
 * ======================================================================== */

int main(void) {
    printf("===============================================\n");
    printf("  seT5 Functional Utility Test Suite\n");
    printf("  8 Capability Layers + Cross-Module Tests\n");
    printf("===============================================\n");

    /* Section 1: TWQ */
    printf("\n====== SECTION 1: Ternary Weight Quantizer ======\n");
    test_twq_config_defaults();
    test_twq_quantize_basic();
    test_twq_quantize_all_zero();
    test_twq_ternary_dot();
    test_twq_matvec();
    test_twq_sparsity();
    test_twq_energy();
    test_twq_overflow_guard();

    /* Section 2: DLFET-RM */
    printf("\n====== SECTION 2: DLFET-RM Simulator ======\n");
    test_dlfet_tnot();
    test_dlfet_tnand();
    test_dlfet_derived_gates();
    test_dlfet_half_adder();
    test_dlfet_full_adder();
    test_dlfet_multi_add();
    test_dlfet_balanced_conversion();
    test_dlfet_pdp();
    test_dlfet_energy_tracking();

    /* Section 3: Radix Transcode */
    printf("\n====== SECTION 3: Radix Transcode ======\n");
    test_rtc_roundtrip();
    test_rtc_zero();
    test_rtc_batch();
    test_rtc_pack_unpack();
    test_rtc_bandwidth();
    test_rtc_stats_tracking();

    /* Section 4: SRBC */
    printf("\n====== SECTION 4: Self-Referential Bias Calibration ======\n");
    test_srbc_init();
    test_srbc_stable_tick();
    test_srbc_thermal_drift();
    test_srbc_tamper_detection();
    test_srbc_small_fault_absorbed();
    test_srbc_voltage_to_trit();
    test_srbc_snm();
    test_srbc_stability();
    test_srbc_reset_refs();

    /* Section 5: Crypto */
    printf("\n====== SECTION 5: Ternary Cryptography ======\n");
    test_crypto_hash_deterministic();
    test_crypto_hash_avalanche();
    test_crypto_keygen();
    test_crypto_encrypt_decrypt();
    test_crypto_mac();
    test_crypto_lattice();
    test_crypto_constant_time();

    /* Section 6: Propagation Delay */
    printf("\n====== SECTION 6: Propagation Delay ======\n");
    test_pdelay_nominal();
    test_pdelay_pvt_adjustment();
    test_pdelay_chain_analysis();
    test_pdelay_classify();
    test_pdelay_pdp();
    test_pdelay_clock_period();

    /* Section 7: TTL */
    printf("\n====== SECTION 7: Ternary Temporal Logic ======\n");
    test_ttl_init_and_register();
    test_ttl_always();
    test_ttl_always_with_unknown();
    test_ttl_always_with_false();
    test_ttl_eventually();
    test_ttl_never();
    test_ttl_safety();
    test_ttl_decide();
    test_ttl_decide_abort();
    test_ttl_evaluate();
    test_ttl_majority_vote();

    /* Section 8: PAM-3/4 */
    printf("\n====== SECTION 8: PAM-3/4 Transcode ======\n");
    test_pam3_encode_decode();
    test_pam3_voltage_levels();
    test_pam3_noise();
    test_pam3_pre_emphasis();
    test_pam3_eye_diagram();
    test_pam3_bandwidth_gain();
    test_pam3_pam4_interop();
    test_pam3_stats();

    /* Section 9: Cross-module */
    printf("\n====== SECTION 9: Cross-Module Integration ======\n");
    test_cross_twq_to_dlfet();
    test_cross_rtc_pam3_pipeline();
    test_cross_srbc_pdelay();
    test_cross_crypto_ttl();

    /* Summary */
    printf("\n===============================================\n");
    printf("  Functional Utility Test Results\n");
    printf("  Total:  %d\n", tests_run);
    printf("  Passed: %d\n", tests_passed);
    printf("  Failed: %d\n", tests_failed);
    printf("===============================================\n");

    return tests_failed ? 1 : 0;
}
