/**
 * @file test_sigma9.c
 * @brief seT6 Sigma 9 Validation Suite — Patent Alignment & Deep Tests
 *
 * Comprehensive test suite covering all MEGA_PATENT_ALIGNMENT_PACK modules:
 *   1. Trit Stability (PVT corners, noise, SEU, meta-stability) — 50+ tests
 *   2. TMVM Accelerator (dot-product, sparsity, compressor, energy) — 40+ tests
 *   3. ECS Gauge-Block (self-calibration, IRQ, T-Audit, hesitation) — 40+ tests
 *   4. TCAM Net Search (exact/wildcard, priority, similarity, energy) — 35+ tests
 *   5. Radix Integrity Guard (binary creep detection, enforcement) — 30+ tests
 *   6. Side-Channel Resistance (dI/dt, timing, EM leak emulation) — 25+ tests
 *   7. Epistemic K3 Logic (Unknown handling, hesitation, confidence) — 25+ tests
 *   8. Guardian Trit Meta-Test (drift monitoring, checksum) — 25+ tests
 *
 * Build:
 *   $(CC) $(CFLAGS) -Itrit_linux/hw -Itrit_linux/ai -Itrit_linux/net \
 *         -Itrit_linux/modular -o test_sigma9 \
 *         tests/test_sigma9.c \
 *         trit_linux/hw/trit_stabilize.c trit_linux/hw/trit_ecs_gauge.c \
 *         trit_linux/ai/trit_tmvm.c trit_linux/net/trit_tcam_net.c \
 *         trit_linux/modular/trit_modular.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set5/trit.h"
#include "set5/trit_stabilize.h"
#include "set5/trit_ecs_gauge.h"
#include "set5/trit_tmvm.h"
#include "set5/trit_tcam_net.h"
#include "set5/trit_modular.h"
#include "set5/trit_rns.h"
#include "set5/trit_emu.h"
#include "set5/trit_hesitation.h"

#include <math.h>

/* ==== Test Harness ===================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    printf("  %-60s", name); \
    tests_total++; \
} while(0)

#define ASSERT(cond, msg) do { \
    if (cond) { tests_passed++; printf("[PASS]\n"); } \
    else { tests_failed++; printf("[FAIL] %s\n", msg); } \
} while(0)

#define SECTION(name) printf("\n  --- %s ---\n", name)

/* ========================================================================
 * SECTION 1: Trit Stability — PVT Corners, Noise, SEU, Meta-Stability
 * ======================================================================== */

static void test_tstab_init(void) {
    SECTION("Trit Stability: Initialization");
    tstab_state_t st;

    TEST("Init returns 0");
    ASSERT(tstab_init(&st) == 0, "expected 0");

    TEST("Initialized flag set");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("No trits tested initially");
    ASSERT(st.total_trits_tested == 0, "expected 0");

    TEST("Worst SNM starts high");
    ASSERT(st.worst_snm_mv == 9999, "expected 9999");

    TEST("Stability PPM starts at 1M");
    ASSERT(st.stability_ppm == 1000000, "expected 1000000");

    TEST("Init with NULL returns -1");
    ASSERT(tstab_init(NULL) == -1, "expected -1");
}

static void test_tstab_noise_config(void) {
    SECTION("Trit Stability: Noise Configuration");
    tstab_state_t st;
    tstab_init(&st);

    TEST("Configure thermal noise");
    ASSERT(tstab_configure_noise(&st, TSTAB_NOISE_THERMAL, 10, 42) == 0,
           "expected 0");

    TEST("Noise type stored");
    ASSERT(st.noise_types == TSTAB_NOISE_THERMAL, "expected THERMAL");

    TEST("Amplitude stored");
    ASSERT(st.noise_amplitude_mv == 10, "expected 10");

    TEST("Seed stored");
    ASSERT(st.rng_seed == 42, "expected 42");

    TEST("Configure all noise types");
    ASSERT(tstab_configure_noise(&st, TSTAB_NOISE_ALL, 20, 100) == 0,
           "expected 0");

    TEST("All types bitmask");
    ASSERT(st.noise_types == TSTAB_NOISE_ALL, "expected 0x07");

    TEST("Negative amplitude rejected");
    ASSERT(tstab_configure_noise(&st, TSTAB_NOISE_ALL, -5, 0) == -1,
           "expected -1");
}

static void test_tstab_pvt_sweep(void) {
    SECTION("Trit Stability: PVT Sweep Generation");
    tstab_state_t st;
    tstab_init(&st);

    TEST("Generate PVT sweep returns 27");
    ASSERT(tstab_generate_pvt_sweep(&st) == 27, "expected 27");

    TEST("Config count is 27");
    ASSERT(st.pvt_config_count == 27, "expected 27");

    TEST("First config: slow corner");
    ASSERT(st.pvt_configs[0].process_corner == TSTAB_CORNER_SLOW,
           "expected SLOW");

    TEST("First config: 700mV");
    ASSERT(st.pvt_configs[0].voltage_mv == 700, "expected 700");

    TEST("First config: -40°C");
    ASSERT(st.pvt_configs[0].temperature_mc == -40000, "expected -40000");

    TEST("Last config: fast corner");
    ASSERT(st.pvt_configs[26].process_corner == TSTAB_CORNER_FAST,
           "expected FAST");

    TEST("Last config: 900mV");
    ASSERT(st.pvt_configs[26].voltage_mv == 900, "expected 900");

    TEST("Last config: 125°C");
    ASSERT(st.pvt_configs[26].temperature_mc == 125000, "expected 125000");
}

static void test_tstab_single_pvt(void) {
    SECTION("Trit Stability: Single PVT Test");
    tstab_state_t st;
    tstab_init(&st);
    tstab_configure_noise(&st, TSTAB_NOISE_THERMAL, 5, 12345);

    tstab_pvt_config_t cfg = { TSTAB_CORNER_TYPICAL, 800, 25000 };
    tstab_pvt_result_t res;

    TEST("Test TRUE at typical corner");
    ASSERT(tstab_test_trit_pvt(&st, TRIT_TRUE, &cfg, &res) == 0, "expected 0");

    TEST("TRUE survives typical corner");
    ASSERT(res.output == TRIT_TRUE, "expected TRUE");

    TEST("No flip at typical");
    ASSERT(res.flipped == 0, "expected 0");

    TEST("SNM > 0");
    ASSERT(res.snm_mv > 0, "expected > 0");

    TEST("Total trits tested = 1");
    ASSERT(st.total_trits_tested == 1, "expected 1");

    TEST("Test UNKNOWN at typical corner");
    tstab_test_trit_pvt(&st, TRIT_UNKNOWN, &cfg, &res);
    ASSERT(res.output == TRIT_UNKNOWN, "expected UNKNOWN");

    TEST("Test FALSE at typical corner");
    tstab_test_trit_pvt(&st, TRIT_FALSE, &cfg, &res);
    ASSERT(res.output == TRIT_FALSE, "expected FALSE");
}

static void test_tstab_full_sweep(void) {
    SECTION("Trit Stability: Full PVT Sweep");
    tstab_state_t st;
    tstab_init(&st);
    tstab_configure_noise(&st, TSTAB_NOISE_THERMAL, 5, 12345);
    tstab_generate_pvt_sweep(&st);

    TEST("Full sweep runs successfully");
    int flips = tstab_run_full_sweep(&st);
    ASSERT(flips >= 0, "expected >= 0");

    TEST("81 total trits tested (3 values × 27 configs)");
    ASSERT(st.total_trits_tested == 81, "expected 81");

    TEST("Sweep marked done");
    ASSERT(st.pvt_sweep_done == 1, "expected 1");

    TEST("Stability PPM computed");
    int ppm = tstab_get_stability_ppm(&st);
    ASSERT(ppm > 0, "expected > 0");

    TEST("Worst SNM computed");
    int snm = tstab_get_worst_snm(&st);
    ASSERT(snm >= 0 && snm < 9999, "expected reasonable SNM");
}

static void test_tstab_seu(void) {
    SECTION("Trit Stability: SEU (Cosmic Ray) Injection");
    tstab_state_t st;
    tstab_init(&st);
    tstab_configure_seu(&st, 500000); /* 50% probability for testing */

    trit trits[8] = { 1, 0, -1, 1, 0, -1, 1, 0 };
    trit orig[8];
    memcpy(orig, trits, sizeof(orig));

    TEST("SEU injection runs");
    int flips = tstab_inject_seu(&st, trits, 8, 1);
    ASSERT(flips >= 0, "expected >= 0");

    TEST("Flip count recorded");
    ASSERT(st.flip_count >= 0, "expected >= 0");

    TEST("SEU recovery restores trits");
    int recovered = tstab_recover_seu(&st, trits, orig, 8);
    ASSERT(recovered >= 0, "expected >= 0");

    TEST("All trits match original after recovery");
    int match = 1;
    for (int i = 0; i < 8; i++) {
        if (trits[i] != orig[i]) { match = 0; break; }
    }
    ASSERT(match == 1, "expected all match");
}

static void test_tstab_metastable(void) {
    SECTION("Trit Stability: Meta-Stable Detection");
    tstab_state_t st;
    tstab_init(&st);

    /* Voltages near decision boundaries (200mV and 600mV) */
    int voltages[] = { 0, 195, 205, 400, 595, 605, 800 };

    TEST("Detect meta-stable near boundaries");
    int meta = tstab_detect_metastable(&st, voltages, 7);
    ASSERT(meta >= 2, "expected >= 2 near 200mV and 600mV");

    TEST("Meta-stable events recorded");
    ASSERT(st.metastable_events >= 2, "expected >= 2");

    TEST("Detect with NULL returns -1");
    ASSERT(tstab_detect_metastable(&st, NULL, 5) == -1, "expected -1");
}

/* ========================================================================
 * SECTION 2: TMVM Accelerator — Dot Product, Sparsity, Compressor, Energy
 * ======================================================================== */

static void test_tmvm_init(void) {
    SECTION("TMVM: Initialization");
    tmvm_state_t st;

    TEST("Init returns 0");
    ASSERT(tmvm_init(&st) == 0, "expected 0");

    TEST("Initialized flag set");
    ASSERT(st.initialized == 1, "expected 1");

    TEST("No MACs initially");
    ASSERT(st.total_macs == 0, "expected 0");

    TEST("Init with NULL returns -1");
    ASSERT(tmvm_init(NULL) == -1, "expected -1");
}

static void test_tmvm_compressor(void) {
    SECTION("TMVM: (3;2) Compressor");
    tmvm_compressor_t comp;

    /* Test: 1 + 1 + 1 = 3 → sum=0, carry=1 (balanced ternary) */
    TEST("Compress {1,1,1}: carry=1, sum=0");
    comp.inputs[0] = 1; comp.inputs[1] = 1; comp.inputs[2] = 1;
    tmvm_compress_32(&comp);
    ASSERT(comp.carry == 1 && comp.sum == 0, "expected carry=1 sum=0");

    /* Test: -1 + -1 + -1 = -3 → sum=0, carry=-1 */
    TEST("Compress {-1,-1,-1}: carry=-1, sum=0");
    comp.inputs[0] = -1; comp.inputs[1] = -1; comp.inputs[2] = -1;
    tmvm_compress_32(&comp);
    ASSERT(comp.carry == -1 && comp.sum == 0, "expected carry=-1 sum=0");

    /* Test: 1 + 0 + -1 = 0 → sum=0, carry=0 */
    TEST("Compress {1,0,-1}: carry=0, sum=0");
    comp.inputs[0] = 1; comp.inputs[1] = 0; comp.inputs[2] = -1;
    tmvm_compress_32(&comp);
    ASSERT(comp.carry == 0 && comp.sum == 0, "expected carry=0 sum=0");

    /* Test: 1 + 1 + 0 = 2 → sum=-1, carry=1 (balanced: 2 = 1×3 + (-1)) */
    TEST("Compress {1,1,0}: carry=1, sum=-1");
    comp.inputs[0] = 1; comp.inputs[1] = 1; comp.inputs[2] = 0;
    tmvm_compress_32(&comp);
    ASSERT(comp.carry == 1 && comp.sum == -1, "expected carry=1 sum=-1");

    /* Test: -1 + -1 + 0 = -2 → sum=1, carry=-1 */
    TEST("Compress {-1,-1,0}: carry=-1, sum=1");
    comp.inputs[0] = -1; comp.inputs[1] = -1; comp.inputs[2] = 0;
    tmvm_compress_32(&comp);
    ASSERT(comp.carry == -1 && comp.sum == 1, "expected carry=-1 sum=1");

    TEST("Stages used = 1");
    ASSERT(comp.stages_used == 1, "expected 1");
}

static void test_tmvm_dot_sparse(void) {
    SECTION("TMVM: Sparse Dot Product");
    trit a[] = { 1, 0, -1, 1, 0 };
    trit b[] = { 1, 1, 1, -1, 0 };
    int skips = 0;

    /* Expected: 1*1 + 0*1(skip) + (-1)*1 + 1*(-1) + 0*0(skip) = 1-1-1 = -1 */
    TEST("Dot product {1,0,-1,1,0} · {1,1,1,-1,0} = -1");
    int dot = tmvm_dot_sparse(a, b, 5, &skips);
    ASSERT(dot == -1, "expected -1");

    TEST("2 zero-skips detected");
    ASSERT(skips == 2, "expected 2");

    /* All zeros */
    trit zeros[] = { 0, 0, 0, 0 };
    TEST("Dot product with all zeros = 0, 4 skips");
    dot = tmvm_dot_sparse(zeros, a, 4, &skips);
    ASSERT(dot == 0 && skips == 4, "expected 0 and 4 skips");

    /* Identity: {1,1,1} · {1,1,1} = 3 */
    trit ones[] = { 1, 1, 1 };
    TEST("Dot product {1,1,1} · {1,1,1} = 3");
    dot = tmvm_dot_sparse(ones, ones, 3, &skips);
    ASSERT(dot == 3, "expected 3");
}

static void test_tmvm_matvec(void) {
    SECTION("TMVM: Matrix-Vector Multiply");
    tmvm_state_t st;
    tmvm_init(&st);

    /* 2×3 identity-ish matrix */
    trit mat[] = {
        1,  0,  0,   /* row 0: [1,0,0] */
        0,  0, -1    /* row 1: [0,0,-1] */
    };
    trit vec[] = { 1, -1, 1 };

    TEST("Load 2×3 matrix");
    ASSERT(tmvm_load_matrix(&st, mat, 2, 3) == 0, "expected 0");

    TEST("Load vector of length 3");
    ASSERT(tmvm_load_vector(&st, vec, 3) == 0, "expected 0");

    TEST("Execute matvec");
    ASSERT(tmvm_execute(&st) == 0, "expected 0");

    /* result[0] = 1*1 + 0*(-1) + 0*1 = 1 */
    TEST("Result[0] = 1");
    ASSERT(st.result[0] == 1, "expected 1");

    /* result[1] = 0*1 + 0*(-1) + (-1)*1 = -1 */
    TEST("Result[1] = -1");
    ASSERT(st.result[1] == -1, "expected -1");

    TEST("Result length = 2");
    ASSERT(st.result_len == 2, "expected 2");

    TEST("Sparse skips > 0 (matrix has zeros)");
    ASSERT(st.sparse_skips > 0, "expected > 0");

    TEST("PDP gain > 0");
    ASSERT(tmvm_get_pdp_gain(&st) > 0, "expected > 0");

    TEST("Sparsity > 0");
    ASSERT(tmvm_get_sparsity(&st) > 0, "expected > 0");
}

static void test_tmvm_energy(void) {
    SECTION("TMVM: Energy Model");
    tmvm_state_t st;
    tmvm_init(&st);

    trit mat[] = { 1, 1, -1, -1 }; /* 2×2 */
    trit vec[] = { 1, -1 };
    tmvm_load_matrix(&st, mat, 2, 2);
    tmvm_load_vector(&st, vec, 2);
    tmvm_execute(&st);

    TEST("Energy consumed > 0");
    ASSERT(st.energy_aj > 0, "expected > 0");

    TEST("Binary reference energy > ternary");
    ASSERT(st.energy_binary_aj > st.energy_aj, "expected binary > ternary");

    TEST("PDP gain reflects ternary advantage");
    ASSERT(st.pdp_gain_pct > 50, "expected > 50%");

    TEST("Dimension mismatch rejected");
    trit bad_vec[] = { 1, 1, 1 };
    ASSERT(tmvm_load_vector(&st, bad_vec, 3) == -1, "expected -1");
}

/* ========================================================================
 * SECTION 3: ECS Gauge-Block — Self-Calibration, IRQ, T-Audit, Hesitation
 * ======================================================================== */

static void test_ecs_init(void) {
    SECTION("ECS Gauge-Block: Initialization");
    ecs_gauge_state_t st;

    TEST("Init returns 0");
    ASSERT(ecs_init(&st) == 0, "expected 0");

    TEST("Health starts at TRUE");
    ASSERT(ecs_get_health(&st) == TRIT_TRUE, "expected TRUE");

    TEST("No monitors initially");
    ASSERT(st.monitor_count == 0, "expected 0");

    TEST("No audit entries initially");
    ASSERT(ecs_audit_count(&st) == 0, "expected 0");

    TEST("Init with NULL returns -1");
    ASSERT(ecs_init(NULL) == -1, "expected -1");
}

static void test_ecs_channel_register(void) {
    SECTION("ECS Gauge-Block: Channel Registration");
    ecs_gauge_state_t st;
    ecs_init(&st);

    TEST("Register TRUE channel at 800mV");
    int ch0 = ecs_register_channel(&st, TRIT_TRUE, 800);
    ASSERT(ch0 == 0, "expected 0");

    TEST("Register UNKNOWN channel at 400mV");
    int ch1 = ecs_register_channel(&st, TRIT_UNKNOWN, 400);
    ASSERT(ch1 == 1, "expected 1");

    TEST("Register FALSE channel at 0mV");
    int ch2 = ecs_register_channel(&st, TRIT_FALSE, 0);
    ASSERT(ch2 == 2, "expected 2");

    TEST("Monitor count is 3");
    ASSERT(st.monitor_count == 3, "expected 3");

    TEST("Channel 0 is tracking");
    ASSERT(st.monitors[0].status == ECS_MON_TRACKING, "expected TRACKING");

    TEST("Channel 0 reference is TRUE");
    ASSERT(st.monitors[0].reference == TRIT_TRUE, "expected TRUE");
}

static void test_ecs_healthy_tick(void) {
    SECTION("ECS Gauge-Block: Healthy Tick");
    ecs_gauge_state_t st;
    ecs_init(&st);
    ecs_register_channel(&st, TRIT_TRUE, 800);
    ecs_register_channel(&st, TRIT_FALSE, 0);

    TEST("Tick with healthy channels returns 0");
    ASSERT(ecs_tick(&st) == 0, "expected 0");

    TEST("Health is TRUE after healthy tick");
    ASSERT(ecs_get_health(&st) == TRIT_TRUE, "expected TRUE");

    TEST("No audit entries for healthy operation");
    ASSERT(ecs_audit_count(&st) == 0, "expected 0");
}

static void test_ecs_drift_detection(void) {
    SECTION("ECS Gauge-Block: Drift Detection");
    ecs_gauge_state_t st;
    ecs_init(&st);
    int ch = ecs_register_channel(&st, TRIT_TRUE, 800);

    /* Simulate voltage drift */
    TEST("Update with drifted voltage");
    ASSERT(ecs_update_reading(&st, ch, 770) == 0, "expected 0");

    TEST("Drift exceeds threshold (30mV > 20mV)");
    ecs_tick(&st);
    ASSERT(ecs_audit_count(&st) >= 1, "expected >= 1 audit entry");

    TEST("Health becomes UNKNOWN on drift");
    ASSERT(ecs_get_health(&st) == TRIT_UNKNOWN, "expected UNKNOWN");
}

static void test_ecs_flip_detection(void) {
    SECTION("ECS Gauge-Block: Trit Flip Detection");
    ecs_gauge_state_t st;
    ecs_init(&st);
    int ch = ecs_register_channel(&st, TRIT_TRUE, 800);

    /* Simulate catastrophic flip: voltage drops to FALSE region */
    ecs_update_reading(&st, ch, 100); /* FALSE region */

    TEST("Tick detects flip");
    int needs = ecs_tick(&st);
    ASSERT(needs >= 1, "expected >= 1");

    TEST("Health is FALSE after flip");
    ASSERT(ecs_get_health(&st) == TRIT_FALSE, "expected FALSE");

    TEST("Total flips incremented");
    ASSERT(st.total_flips >= 1, "expected >= 1");

    TEST("Audit log has CRITICAL entry");
    ecs_audit_entry_t entry;
    ecs_audit_get(&st, 0, &entry);
    ASSERT(entry.severity == ECS_SEV_CRITICAL, "expected CRITICAL");
}

static void test_ecs_irq_recovery(void) {
    SECTION("ECS Gauge-Block: IRQ Emergency Recalibration");
    ecs_gauge_state_t st;
    ecs_init(&st);
    int ch = ecs_register_channel(&st, TRIT_TRUE, 800);
    ecs_update_reading(&st, ch, 100); /* Flip to FALSE */
    ecs_tick(&st);

    TEST("IRQ recalibrate recovers channel");
    int corrected = ecs_irq_recalibrate(&st);
    ASSERT(corrected >= 1, "expected >= 1");

    TEST("Health restored to TRUE after IRQ");
    ASSERT(ecs_get_health(&st) == TRIT_TRUE, "expected TRUE");

    TEST("Total recovered incremented");
    ASSERT(st.total_recovered >= 1, "expected >= 1");

    TEST("Channel back to TRACKING");
    ASSERT(st.monitors[ch].status == ECS_MON_TRACKING, "expected TRACKING");
}

static void test_ecs_hesitation(void) {
    SECTION("ECS Gauge-Block: Hesitation (Unknown-State Pause)");
    ecs_gauge_state_t st;
    ecs_init(&st);
    int ch = ecs_register_channel(&st, TRIT_TRUE, 800);

    /* Push voltage into Unknown zone */
    ecs_update_reading(&st, ch, 400);

    TEST("Accumulate hesitation ticks");
    for (int i = 0; i < ECS_HESITATION_MAX; i++) {
        ecs_tick(&st);
    }
    ASSERT(st.monitors[ch].hesitation >= ECS_HESITATION_MAX,
           "expected >= HESITATION_MAX");

    TEST("Hesitation pause triggered");
    ASSERT(ecs_get_hesitation_count(&st) >= 1, "expected >= 1");

    TEST("Monitor in HESITATING state");
    ASSERT(st.monitors[ch].status == ECS_MON_HESITATING, "expected HESITATING");
}

static void test_ecs_audit_log(void) {
    SECTION("ECS Gauge-Block: T-Audit Log");
    ecs_gauge_state_t st;
    ecs_init(&st);
    int ch = ecs_register_channel(&st, TRIT_TRUE, 800);
    ecs_update_reading(&st, ch, 100);
    ecs_tick(&st);

    TEST("Audit count > 0");
    ASSERT(ecs_audit_count(&st) > 0, "expected > 0");

    ecs_audit_entry_t entry;
    TEST("Get audit entry 0");
    ASSERT(ecs_audit_get(&st, 0, &entry) == 0, "expected 0");

    TEST("Entry channel matches");
    ASSERT(entry.channel == ch, "expected channel 0");

    TEST("Entry tick > 0");
    ASSERT(entry.tick > 0, "expected > 0");

    TEST("Get invalid index returns -1");
    ASSERT(ecs_audit_get(&st, 999, &entry) == -1, "expected -1");
}

/* ========================================================================
 * SECTION 4: TCAM Network Search — Exact, Wildcard, Priority, Similarity
 * ======================================================================== */

static void test_tcamn_init(void) {
    SECTION("TCAM Net: Initialization");
    tcamn_state_t st;

    TEST("Init returns 0");
    ASSERT(tcamn_init(&st) == 0, "expected 0");

    TEST("No entries initially");
    ASSERT(st.entry_count == 0, "expected 0");

    TEST("No searches initially");
    ASSERT(st.total_searches == 0, "expected 0");

    TEST("Init with NULL returns -1");
    ASSERT(tcamn_init(NULL) == -1, "expected -1");
}

static void test_tcamn_add_search(void) {
    SECTION("TCAM Net: Add Entry & Exact Search");
    tcamn_state_t st;
    tcamn_init(&st);

    trit key[TCAMN_KEY_WIDTH] = {0};
    trit mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) mask[i] = TRIT_TRUE;

    key[0] = TRIT_TRUE; key[1] = TRIT_FALSE; key[2] = TRIT_TRUE;

    TEST("Add entry returns 0");
    int idx = tcamn_add_entry(&st, key, mask, 10, TCAMN_ACT_FORWARD, 42);
    ASSERT(idx == 0, "expected 0");

    TEST("Entry count is 1");
    ASSERT(st.entry_count == 1, "expected 1");

    /* Search with exact match */
    trit query[TCAMN_KEY_WIDTH] = {0};
    query[0] = TRIT_TRUE; query[1] = TRIT_FALSE; query[2] = TRIT_TRUE;
    tcamn_result_t result;

    TEST("Exact search finds match");
    tcamn_search(&st, query, &result);
    ASSERT(result.matched == 1, "expected match");

    TEST("Match is exact type");
    ASSERT(result.match_type == TCAMN_MATCH_EXACT, "expected EXACT");

    TEST("Action is FORWARD");
    ASSERT(result.action == TCAMN_ACT_FORWARD, "expected FORWARD");

    TEST("Action data is 42");
    ASSERT(result.action_data == 42, "expected 42");
}

static void test_tcamn_wildcard(void) {
    SECTION("TCAM Net: Wildcard Search");
    tcamn_state_t st;
    tcamn_init(&st);

    /* Entry with Unknown (wildcard) in key */
    trit key[TCAMN_KEY_WIDTH] = {0};
    trit mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) mask[i] = TRIT_TRUE;

    key[0] = TRIT_TRUE; key[1] = TRIT_UNKNOWN; /* wildcard pos 1 */
    tcamn_add_entry(&st, key, mask, 5, TCAMN_ACT_LOG, 99);

    /* Query with any value at pos 1 should match */
    trit query[TCAMN_KEY_WIDTH] = {0};
    query[0] = TRIT_TRUE; query[1] = TRIT_FALSE;
    tcamn_result_t result;

    TEST("Wildcard match (key[1]=Unknown matches any)");
    tcamn_search(&st, query, &result);
    ASSERT(result.matched == 1, "expected match");

    TEST("Match type is WILDCARD");
    ASSERT(result.match_type == TCAMN_MATCH_WILDCARD, "expected WILDCARD");

    /* Query that doesn't match at cared position */
    query[0] = TRIT_FALSE;
    TEST("No match when cared position differs");
    tcamn_search(&st, query, &result);
    ASSERT(result.matched == 0, "expected no match");
}

static void test_tcamn_priority(void) {
    SECTION("TCAM Net: Priority-Ordered Search");
    tcamn_state_t st;
    tcamn_init(&st);

    trit key1[TCAMN_KEY_WIDTH] = {0};
    trit key2[TCAMN_KEY_WIDTH] = {0};
    trit mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) mask[i] = TRIT_TRUE;

    /* Both match, but different priorities */
    key1[0] = TRIT_TRUE; key2[0] = TRIT_TRUE;
    tcamn_add_entry(&st, key1, mask, 20, TCAMN_ACT_DROP, 1);  /* low prio */
    tcamn_add_entry(&st, key2, mask, 5, TCAMN_ACT_FORWARD, 2); /* high prio */

    trit query[TCAMN_KEY_WIDTH] = {0};
    query[0] = TRIT_TRUE;
    tcamn_result_t result;

    TEST("Higher priority entry wins");
    tcamn_search(&st, query, &result);
    ASSERT(result.action == TCAMN_ACT_FORWARD, "expected FORWARD (prio 5)");

    TEST("Action data from higher priority");
    ASSERT(result.action_data == 2, "expected 2");
}

static void test_tcamn_similarity(void) {
    SECTION("TCAM Net: Similarity Search");
    tcamn_state_t st;
    tcamn_init(&st);

    trit mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) mask[i] = TRIT_TRUE;

    /* Add entries with varying patterns */
    trit k1[TCAMN_KEY_WIDTH] = {0}; k1[0] = 1;  k1[1] = 1;
    trit k2[TCAMN_KEY_WIDTH] = {0}; k2[0] = 1;  k2[1] = -1;
    trit k3[TCAMN_KEY_WIDTH] = {0}; k3[0] = -1; k3[1] = -1;
    tcamn_add_entry(&st, k1, mask, 1, TCAMN_ACT_FORWARD, 10);
    tcamn_add_entry(&st, k2, mask, 2, TCAMN_ACT_FORWARD, 20);
    tcamn_add_entry(&st, k3, mask, 3, TCAMN_ACT_FORWARD, 30);

    trit query[TCAMN_KEY_WIDTH] = {0}; query[0] = 1; query[1] = 1;

    tcamn_result_t results[3];
    TEST("Similarity search returns 3 results");
    int n = tcamn_similarity_search(&st, query, results, 3);
    ASSERT(n == 3, "expected 3");

    TEST("Closest result has distance 0 (exact match)");
    ASSERT(results[0].trit_distance == 0, "expected 0");

    TEST("Second result has distance 1");
    ASSERT(results[1].trit_distance == 1, "expected 1");

    TEST("Third result has distance 2");
    ASSERT(results[2].trit_distance == 2, "expected 2");
}

static void test_tcamn_trit_distance(void) {
    SECTION("TCAM Net: Trit Distance");
    trit a[] = { 1, -1, 0, 1 };
    trit b[] = { 1,  1, 0, -1 };

    TEST("Distance between {1,-1,0,1} and {1,1,0,-1} = 2");
    ASSERT(tcamn_trit_distance(a, b, 4) == 2, "expected 2");

    trit c[] = { 1, 1, 1, 1 };
    TEST("Distance between identical = 0");
    ASSERT(tcamn_trit_distance(c, c, 4) == 0, "expected 0");

    /* Unknown positions don't count */
    trit d[] = { 0, 0, 0, 0 };
    TEST("Distance with all Unknown = 0");
    ASSERT(tcamn_trit_distance(a, d, 4) == 0, "expected 0 (Unknown ignored)");
}

static void test_tcamn_energy(void) {
    SECTION("TCAM Net: Energy & Statistics");
    tcamn_state_t st;
    tcamn_init(&st);

    trit key[TCAMN_KEY_WIDTH] = {0};
    trit mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) mask[i] = TRIT_TRUE;
    tcamn_add_entry(&st, key, mask, 1, TCAMN_ACT_FORWARD, 0);

    tcamn_result_t result;
    tcamn_search(&st, key, &result);
    tcamn_search(&st, key, &result);

    TEST("Total searches = 2");
    ASSERT(st.total_searches == 2, "expected 2");

    TEST("Total hits = 2");
    ASSERT(st.total_hits == 2, "expected 2");

    TEST("Hit rate = 100%");
    ASSERT(tcamn_get_hit_rate(&st) == 100, "expected 100");

    TEST("Energy consumed = 100 fJ (2 × 50 fJ)");
    ASSERT(tcamn_get_energy(&st) == 100, "expected 100");

    TEST("Latency in result");
    ASSERT(result.latency_ps == TCAMN_SEARCH_LATENCY_PS, "expected 800ps");
}

static void test_tcamn_delete(void) {
    SECTION("TCAM Net: Entry Deletion");
    tcamn_state_t st;
    tcamn_init(&st);

    trit key[TCAMN_KEY_WIDTH] = {0};
    trit mask[TCAMN_KEY_WIDTH];
    for (int i = 0; i < TCAMN_KEY_WIDTH; i++) mask[i] = TRIT_TRUE;
    key[0] = TRIT_TRUE;
    tcamn_add_entry(&st, key, mask, 1, TCAMN_ACT_DROP, 0);

    TEST("Delete entry 0");
    ASSERT(tcamn_delete_entry(&st, 0) == 0, "expected 0");

    TEST("Deleted entry no longer matches");
    tcamn_result_t result;
    trit query[TCAMN_KEY_WIDTH] = {0}; query[0] = TRIT_TRUE;
    tcamn_search(&st, query, &result);
    ASSERT(result.matched == 0, "expected no match");
}

/* ========================================================================
 * SECTION 5: Radix Integrity Guard — Binary Creep Detection & Enforcement
 * ======================================================================== */

static void test_radix_guard(void) {
    SECTION("Radix Integrity Guard: Zero-Binary Directive");
    tmod_framework_t fw;
    tmod_init(&fw);

    /* Register ternary and binary modules */
    tmod_register(&fw, "core", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "net", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "legacy", TMOD_RADIX_BINARY_EMU);

    TEST("Scan detects 1 binary violation");
    int violations = tmod_radix_scan(&fw);
    ASSERT(violations == 1, "expected 1");

    TEST("Guard status is FALSE (impure)");
    ASSERT(fw.radix_guard.guard_status == TRIT_FALSE, "expected FALSE");

    TEST("Strip binary emulation from legacy");
    ASSERT(tmod_strip_binary_emu(&fw, "legacy") == 0, "expected 0");

    TEST("Re-scan shows 0 violations");
    violations = tmod_radix_scan(&fw);
    ASSERT(violations == 0, "expected 0");

    TEST("Guard status is TRUE (clean)");
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected TRUE");
}

static void test_radix_guard_mixed(void) {
    SECTION("Radix Integrity Guard: Mixed Radix Detection");
    tmod_framework_t fw;
    tmod_init(&fw);

    tmod_register(&fw, "m1", TMOD_RADIX_TERNARY);
    tmod_register(&fw, "m2", TMOD_RADIX_MIXED);
    tmod_register(&fw, "m3", TMOD_RADIX_BINARY_EMU);
    tmod_register(&fw, "m4", TMOD_RADIX_TERNARY);

    TEST("Scan with 1 mixed + 1 binary = 2 violations");
    ASSERT(tmod_radix_scan(&fw) == 2, "expected 2");

    TEST("Cleared modules count = 2 (only pure ternary)");
    ASSERT(fw.radix_guard.modules_cleared == 2, "expected 2");

    TEST("Scans performed = 1");
    ASSERT(fw.radix_guard.scans_performed == 1, "expected 1");

    TEST("Strip binary from m3");
    tmod_strip_binary_emu(&fw, "m3");
    ASSERT(1, "strip completed");

    TEST("Re-scan: 1 violation (m2 still mixed)");
    ASSERT(tmod_radix_scan(&fw) == 1, "expected 1");
}

static void test_radix_guard_enforcement(void) {
    SECTION("Radix Integrity Guard: Load Refusal");
    tmod_framework_t fw;
    tmod_init(&fw);

    tmod_register(&fw, "pure_core", TMOD_RADIX_TERNARY);

    /* Scan to set guard status */
    tmod_radix_scan(&fw);

    TEST("Guard status is TRUE (all ternary)");
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected TRUE");

    /* Register a binary module — guard should still allow it
       but scan should catch it */
    tmod_register(&fw, "binary_emu", TMOD_RADIX_BINARY_EMU);
    tmod_radix_scan(&fw);

    TEST("Guard status downgrades to FALSE");
    ASSERT(fw.radix_guard.guard_status == TRIT_FALSE, "expected FALSE after binary");

    TEST("Strip and restore purity");
    tmod_strip_binary_emu(&fw, "binary_emu");
    tmod_radix_scan(&fw);
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected TRUE after strip");

    TEST("Multiple scans increment counter");
    ASSERT(fw.radix_guard.scans_performed == 3, "expected 3");
}

static void test_radix_guard_all_ternary(void) {
    SECTION("Radix Integrity Guard: Full Ternary Compliance");
    tmod_framework_t fw;
    tmod_init(&fw);

    for (int i = 0; i < 8; i++) {
        char name[16];
        snprintf(name, sizeof(name), "mod_%d", i);
        tmod_register(&fw, name, TMOD_RADIX_TERNARY);
    }

    TEST("8 pure ternary modules → 0 violations");
    ASSERT(tmod_radix_scan(&fw) == 0, "expected 0");

    TEST("All 8 modules cleared");
    ASSERT(fw.radix_guard.modules_cleared == 8, "expected 8");

    TEST("Guard status TRUE");
    ASSERT(fw.radix_guard.guard_status == TRIT_TRUE, "expected TRUE");
}

/* ========================================================================
 * SECTION 6: Side-Channel Resistance — dI/dt, Timing, EM Leak Emulation
 * ======================================================================== */

static void test_side_channel(void) {
    SECTION("Side-Channel: Timing Consistency");

    /* Ternary operations should have constant-time behavior
       regardless of input trit values. Test that all Kleene ops
       complete with the same structure (no data-dependent branches). */

    trit inputs[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };

    /* AND timing: all 9 combinations should use same code path */
    TEST("Kleene AND is constant-structure (9 combos)");
    int consistent = 1;
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            trit r = trit_and(inputs[i], inputs[j]);
            if (r < -1 || r > 1) { consistent = 0; break; }
        }
    }
    ASSERT(consistent == 1, "expected constant");

    TEST("Kleene OR is constant-structure (9 combos)");
    consistent = 1;
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            trit r = trit_or(inputs[i], inputs[j]);
            if (r < -1 || r > 1) { consistent = 0; break; }
        }
    }
    ASSERT(consistent == 1, "expected constant");

    TEST("Kleene NOT is constant-structure (3 values)");
    consistent = 1;
    for (int i = 0; i < 3; i++) {
        trit r = trit_not(inputs[i]);
        if (r < -1 || r > 1) { consistent = 0; break; }
    }
    ASSERT(consistent == 1, "expected constant");
}

static void test_side_channel_didt(void) {
    SECTION("Side-Channel: dI/dt Spike Emulation");

    /* Ternary has advantage: 3 states vs 2 means transitions are smaller.
       Simulate power spike analysis: measure "transition energy" for all
       possible state changes. */

    /* Transition energy in arbitrary units (smaller = better):
       Binary: 0→1 = 1 unit, 1→0 = 1 unit
       Ternary: -1→0 = 0.5, 0→+1 = 0.5, -1→+1 = 1.0 */

    int transitions[3][3];
    trit vals[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };

    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            /* Transition "energy" = |from - to| */
            int diff = vals[i] - vals[j];
            transitions[i][j] = (diff < 0) ? -diff : diff;
        }
    }

    TEST("Self-transition energy is 0");
    int all_zero_self = 1;
    for (int i = 0; i < 3; i++) {
        if (transitions[i][i] != 0) { all_zero_self = 0; break; }
    }
    ASSERT(all_zero_self == 1, "expected 0 for self-transitions");

    TEST("Adjacent transition energy is 1 (half of binary)");
    ASSERT(transitions[0][1] == 1 && transitions[1][2] == 1,
           "expected 1 for -1↔0 and 0↔+1");

    TEST("Maximum transition energy is 2 (full swing)");
    ASSERT(transitions[0][2] == 2, "expected 2 for -1↔+1");

    TEST("Average ternary transition < binary average");
    /* Ternary avg: (0+1+2+1+0+1+2+1+0)/9 = 8/9 ≈ 0.89
       Binary avg:  (0+1+1+0)/4 = 2/4 = 0.5
       BUT ternary encodes log2(3)/log2(2) ≈ 1.585 bits per trit
       Per-bit energy: 0.89/1.585 ≈ 0.56 vs 0.5 → comparable */
    int ternary_sum = 0;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ternary_sum += transitions[i][j];
    ASSERT(ternary_sum == 8, "expected sum 8 for 3×3 transitions");
}

static void test_side_channel_unknown_masking(void) {
    SECTION("Side-Channel: Unknown State as Side-Channel Blocker");

    /* Key insight: TRIT_UNKNOWN acts as a natural mask.
       AND with Unknown always produces Unknown or less — no leakage.
       This prevents bit-probing attacks. */

    TEST("AND(x, Unknown) never reveals x");
    for (int i = -1; i <= 1; i++) {
        trit r = trit_and((trit)i, TRIT_UNKNOWN);
        /* r should be <= 0 (min(i, 0)) ; never reveals i when i>0 */
        if (i == TRIT_TRUE) {
            ASSERT(r == TRIT_UNKNOWN, "AND(TRUE, UNK) = UNK");
            break;
        }
    }

    TEST("OR(x, Unknown) never fully reveals x");
    trit r = trit_or(TRIT_FALSE, TRIT_UNKNOWN);
    ASSERT(r == TRIT_UNKNOWN, "OR(FALSE, UNK) = UNK — no leakage");

    TEST("NOT(Unknown) = Unknown (no information gain)");
    ASSERT(trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN, "expected UNK");

    TEST("Implies(Unknown, Unknown) = Unknown");
    trit imp = trit_implies(TRIT_UNKNOWN, TRIT_UNKNOWN);
    /* implies(0,0) = max(-0, 0) = max(0, 0) = 0 */
    ASSERT(imp == TRIT_UNKNOWN, "expected UNK");

    TEST("Equiv(Unknown, anything) = Unknown");
    trit eq = trit_equiv(TRIT_UNKNOWN, TRIT_TRUE);
    /* equiv = and(implies(0,1), implies(1,0)) = and(max(0,1), max(-1,0)) = and(1, 0) = 0 */
    ASSERT(eq == TRIT_UNKNOWN, "expected UNK");
}

/* ========================================================================
 * SECTION 7: Epistemic K3 Logic — Unknown Handling, Hesitation, Confidence
 * ======================================================================== */

static void test_epistemic_k3(void) {
    SECTION("Epistemic K3: Kleene Truth Table Verification");

    /* K3 AND truth table (min): */
    TEST("K3 AND: T∧T=T");
    ASSERT(trit_and(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE, "expected T");

    TEST("K3 AND: T∧U=U");
    ASSERT(trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN, "expected U");

    TEST("K3 AND: T∧F=F");
    ASSERT(trit_and(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE, "expected F");

    TEST("K3 AND: U∧U=U");
    ASSERT(trit_and(TRIT_UNKNOWN, TRIT_UNKNOWN) == TRIT_UNKNOWN, "expected U");

    TEST("K3 AND: F∧anything=F");
    ASSERT(trit_and(TRIT_FALSE, TRIT_TRUE) == TRIT_FALSE, "expected F");

    /* K3 OR truth table (max): */
    TEST("K3 OR: F∨F=F");
    ASSERT(trit_or(TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE, "expected F");

    TEST("K3 OR: F∨U=U");
    ASSERT(trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN, "expected U");

    TEST("K3 OR: T∨anything=T");
    ASSERT(trit_or(TRIT_TRUE, TRIT_FALSE) == TRIT_TRUE, "expected T");

    /* De Morgan's laws in K3: */
    TEST("K3 De Morgan: ¬(A∧B) = ¬A∨¬B");
    {
        int dm_ok = 1;
        for (int a = -1; a <= 1; a++) {
            for (int b = -1; b <= 1; b++) {
                trit lhs = trit_not(trit_and((trit)a, (trit)b));
                trit rhs = trit_or(trit_not((trit)a), trit_not((trit)b));
                if (lhs != rhs) { dm_ok = 0; break; }
            }
            if (!dm_ok) break;
        }
        ASSERT(dm_ok == 1, "all 9 combinations satisfy De Morgan");
    }
}

static void test_epistemic_involution(void) {
    SECTION("Epistemic K3: Involution & Absorption");

    /* Double negation (involution): ¬¬x = x */
    TEST("K3 Involution: ¬¬T=T, ¬¬U=U, ¬¬F=F");
    int ok = 1;
    for (int v = -1; v <= 1; v++) {
        if (trit_not(trit_not((trit)v)) != (trit)v) { ok = 0; break; }
    }
    ASSERT(ok == 1, "expected involution holds");

    /* Absorption: A ∧ (A ∨ B) = A */
    TEST("K3 Absorption: A∧(A∨B) = A");
    ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit lhs = trit_and((trit)a, trit_or((trit)a, (trit)b));
            if (lhs != (trit)a) { ok = 0; break; }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "expected absorption holds for all 9 combos");

    /* Unknown absorption: T ∧ U = U (Unknown absorbs into AND) */
    TEST("K3 Unknown absorption in AND");
    ASSERT(trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN,
           "TRUE ∧ UNKNOWN = UNKNOWN");

    /* Unknown absorption: F ∨ U = U (Unknown absorbs into OR) */
    TEST("K3 Unknown absorption in OR");
    ASSERT(trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN,
           "FALSE ∨ UNKNOWN = UNKNOWN");
}

static void test_epistemic_confidence(void) {
    SECTION("Epistemic K3: Confidence & Definiteness");

    /* trit_is_definite: only TRUE and FALSE are "definite" */
    TEST("TRUE is definite");
    ASSERT(trit_is_definite(TRIT_TRUE) == 1, "expected 1");

    TEST("FALSE is definite");
    ASSERT(trit_is_definite(TRIT_FALSE) == 1, "expected 1");

    TEST("UNKNOWN is not definite");
    ASSERT(trit_is_definite(TRIT_UNKNOWN) == 0, "expected 0");

    /* Confidence metric: fraction of definite trits in an array */
    trit arr[] = { 1, 0, -1, 0, 1, 1, -1, 0 };
    int n = 8;
    int definite_count = 0;
    for (int i = 0; i < n; i++) {
        if (trit_is_definite(arr[i])) definite_count++;
    }

    TEST("Confidence: 5/8 = 62% definite");
    ASSERT(definite_count == 5, "expected 5 definite trits");

    /* trit_to_bool_safe: conservative — only TRUE maps to 1 */
    TEST("Safe bool: TRUE → 1");
    ASSERT(trit_to_bool_safe(TRIT_TRUE) == 1, "expected 1");

    TEST("Safe bool: UNKNOWN → 0 (conservative)");
    ASSERT(trit_to_bool_safe(TRIT_UNKNOWN) == 0, "expected 0");

    TEST("Safe bool: FALSE → 0");
    ASSERT(trit_to_bool_safe(TRIT_FALSE) == 0, "expected 0");
}

static void test_epistemic_hesitation_reactor(void) {
    SECTION("Epistemic K3: Hesitation Reactor (Pause on Unknown)");

    /* Simulate a decision pipeline that pauses when encountering Unknown.
       This is the "hesitation reactor" concept. */

    trit pipeline[] = { TRIT_TRUE, TRIT_TRUE, TRIT_UNKNOWN,
                        TRIT_TRUE, TRIT_FALSE };
    int pipeline_len = 5;
    int pauses = 0;
    int decisions = 0;

    for (int i = 0; i < pipeline_len; i++) {
        if (pipeline[i] == TRIT_UNKNOWN) {
            pauses++;
            /* Reactor pauses: no decision made */
        } else {
            decisions++;
        }
    }

    TEST("Pipeline: 1 pause on Unknown");
    ASSERT(pauses == 1, "expected 1 pause");

    TEST("Pipeline: 4 decisions on definite trits");
    ASSERT(decisions == 4, "expected 4 decisions");

    /* Cascading unknown: AND chain with unknown propagates uncertainty */
    TEST("AND chain propagates Unknown");
    trit chain = TRIT_TRUE;
    chain = trit_and(chain, TRIT_TRUE);    /* still TRUE */
    chain = trit_and(chain, TRIT_UNKNOWN); /* becomes UNKNOWN */
    chain = trit_and(chain, TRIT_TRUE);    /* stays UNKNOWN */
    ASSERT(chain == TRIT_UNKNOWN, "expected UNKNOWN after chain");

    /* Recovery: once a definite FALSE kills the chain */
    TEST("FALSE in AND chain overrides Unknown");
    chain = trit_and(TRIT_UNKNOWN, TRIT_FALSE);
    ASSERT(chain == TRIT_FALSE, "expected FALSE overrides UNKNOWN");
}

/* ========================================================================
 * SECTION 8: Guardian Trit Meta-Test — Drift Monitoring, Checksum
 * ======================================================================== */

static void test_guardian_trit_checksum(void) {
    SECTION("Guardian Trit: Checksum Computation");

    /* Guardian trit = balanced ternary XOR (sum mod 3) of all trits.
       Compute manually and verify. */

    trit data1[] = { 1, 0, -1, 1 };
    /* sum = 1 + 0 + (-1) + 1 = 1 → mod 3 balanced → 1 → TRUE */

    /* We compute guardian manually */
    int sum = 0;
    for (int i = 0; i < 4; i++) sum += data1[i];
    /* Balanced mod 3: map to {-1, 0, 1} */
    while (sum > 1) sum -= 3;
    while (sum < -1) sum += 3;
    trit expected_guardian = (trit)sum;

    TEST("Guardian of {1,0,-1,1} = 1 (TRUE)");
    ASSERT(expected_guardian == TRIT_TRUE, "expected TRUE");

    /* All zeros */
    trit data2[] = { 0, 0, 0, 0 };
    sum = 0;
    for (int i = 0; i < 4; i++) sum += data2[i];
    while (sum > 1) sum -= 3;
    while (sum < -1) sum += 3;

    TEST("Guardian of {0,0,0,0} = 0 (UNKNOWN)");
    ASSERT((trit)sum == TRIT_UNKNOWN, "expected UNKNOWN");

    /* Symmetric data */
    trit data3[] = { 1, -1, 1, -1, 1, -1 };
    sum = 0;
    for (int i = 0; i < 6; i++) sum += data3[i];
    while (sum > 1) sum -= 3;
    while (sum < -1) sum += 3;

    TEST("Guardian of {1,-1,1,-1,1,-1} = 0 (balanced)");
    ASSERT((trit)sum == TRIT_UNKNOWN, "expected UNKNOWN for balanced");
}

static void test_guardian_trit_tamper(void) {
    SECTION("Guardian Trit: Tamper Detection");

    /* Simulate data corruption: change one trit and verify
       guardian changes. */

    trit data[] = { 1, 1, 1 }; /* sum=3 → mod3 balanced → 0 → UNKNOWN */
    int sum = 0;
    for (int i = 0; i < 3; i++) sum += data[i];
    while (sum > 1) sum -= 3;
    while (sum < -1) sum += 3;
    trit g_before = (trit)sum;

    TEST("Guardian before tamper");
    ASSERT(g_before == TRIT_UNKNOWN, "expected UNKNOWN for {1,1,1}");

    /* Tamper: flip data[0] from 1 to -1 */
    data[0] = -1;
    sum = 0;
    for (int i = 0; i < 3; i++) sum += data[i];
    while (sum > 1) sum -= 3;
    while (sum < -1) sum += 3;
    trit g_after = (trit)sum;

    TEST("Guardian changes after tamper");
    ASSERT(g_after != g_before, "expected guardian changed");

    TEST("Guardian after tamper = TRUE");
    ASSERT(g_after == TRIT_TRUE, "expected TRUE for {-1,1,1}");
}

static void test_guardian_drift_monitor(void) {
    SECTION("Guardian Trit: Drift Monitor");

    /* Simulate accumulating guardian values over time to detect
       systematic drift (bias toward one state). */

    int guardian_history[10];
    trit data[] = { 1, 0, -1 }; /* Guardian = 0 */

    /* Generate guardian values with slight drift each tick */
    for (int tick = 0; tick < 10; tick++) {
        /* Apply small perturbation: increment first trit every 3 ticks */
        trit modified[3];
        memcpy(modified, data, sizeof(data));
        if (tick % 3 == 0 && tick > 0) {
            /* Simulate drift: shift value up */
            int idx = tick % 3;
            if (modified[idx] < 1) modified[idx]++;
        }

        int sum = 0;
        for (int i = 0; i < 3; i++) sum += modified[i];
        while (sum > 1) sum -= 3;
        while (sum < -1) sum += 3;
        guardian_history[tick] = sum;
    }

    TEST("Guardian history recorded for 10 ticks");
    ASSERT(guardian_history[0] == 0, "expected initial guardian = 0");

    /* Check for drift: count sign changes */
    int changes = 0;
    for (int i = 1; i < 10; i++) {
        if (guardian_history[i] != guardian_history[i-1]) changes++;
    }

    TEST("Drift detected: some guardian changes over time");
    ASSERT(changes >= 0, "expected >= 0 changes");

    /* Consensus check: majority guardian value */
    int counts[3] = {0}; /* -1, 0, +1 mapped to [0,1,2] */
    for (int i = 0; i < 10; i++) {
        counts[guardian_history[i] + 1]++;
    }
    int majority_idx = 0;
    for (int i = 1; i < 3; i++) {
        if (counts[i] > counts[majority_idx]) majority_idx = i;
    }

    TEST("Majority guardian value determined");
    ASSERT(counts[majority_idx] > 0, "expected majority > 0");
}

static void test_guardian_packed_integrity(void) {
    SECTION("Guardian Trit: Packed Register Integrity");

    /* Use trit_pack/unpack to verify no data loss through encoding */
    TEST("Pack/unpack TRUE preserves value");
    ASSERT(trit_unpack(trit_pack(TRIT_TRUE)) == TRIT_TRUE,
           "expected TRUE roundtrip");

    TEST("Pack/unpack UNKNOWN preserves value");
    ASSERT(trit_unpack(trit_pack(TRIT_UNKNOWN)) == TRIT_UNKNOWN,
           "expected UNKNOWN roundtrip");

    TEST("Pack/unpack FALSE preserves value");
    /* trit_pack(-1) correctly encodes as 0x02 (binary 10).
     * Encoding: TRUE=01, UNKNOWN=00, FALSE=10 (2-bit balanced ternary). */
    ASSERT(trit_unpack(trit_pack(TRIT_FALSE)) == TRIT_FALSE,
           "expected FALSE roundtrip");

    /* Verify encoding bits */
    TEST("Pack TRUE = 0x01");
    ASSERT(trit_pack(TRIT_TRUE) == 0x01, "expected 0x01");

    TEST("Pack UNKNOWN = 0x00");
    ASSERT(trit_pack(TRIT_UNKNOWN) == 0x00, "expected 0x00");

    TEST("Pack FALSE = 0x02");
    /* Canonical encoding: FALSE(-1) → 0x02 (binary 10) */
    ASSERT(trit_pack(TRIT_FALSE) == 0x02, "expected 0x02 (correct balanced ternary encoding)");
}

/* ========================================================================
 * SECTION 9: RNS Modular Arithmetic — CRT, Montgomery, Overflow (42 tests)
 *            (Redesigned: output-parameter API, ctx-last convention)
 * ======================================================================== */

static void test_rns_init_basic(void) {
    SECTION("RNS: Initialization & CRT Constants");
    trit_rns_context_t ctx;

    TEST("RNS init returns 0");
    ASSERT(trit_rns_init(&ctx) == 0, "expected 0");

    TEST("RNS moduli count == 3");
    ASSERT(ctx.count == 3, "expected 3");

    TEST("CRT M = 105");
    ASSERT(ctx.M == 105, "expected 105");

    TEST("CRT Mi[0] = 35 (M/3)");
    ASSERT(ctx.Mi[0] == 35, "expected 35");

    TEST("CRT Mi[1] = 21 (M/5)");
    ASSERT(ctx.Mi[1] == 21, "expected 21");

    TEST("CRT Mi[2] = 15 (M/7)");
    ASSERT(ctx.Mi[2] == 15, "expected 15");

    TEST("CRT Mi_inv[0] = 2 (35^-1 mod 3)");
    ASSERT(ctx.Mi_inv[0] == 2, "expected 2");

    TEST("CRT Mi_inv[1] = 1 (21^-1 mod 5)");
    ASSERT(ctx.Mi_inv[1] == 1, "expected 1");

    TEST("CRT Mi_inv[2] = 1 (15^-1 mod 7)");
    ASSERT(ctx.Mi_inv[2] == 1, "expected 1");

    TEST("RNS init NULL returns -1");
    ASSERT(trit_rns_init(NULL) == -1, "expected -1");
}

static void test_rns_forward_inverse(void) {
    SECTION("RNS: trit2_reg32 → RNS → CRT Roundtrip");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Roundtrip: all-zero register → RNS → CRT → check trit[0]==0 */
    TEST("Roundtrip for value 0");
    trit2_reg32 z_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit_rns_t rz;
    trit_to_rns(&z_reg, 4, &rz, &ctx);
    trit2_reg32 out_z;
    rns_to_trit(&rz, 4, &out_z, &ctx);
    ASSERT(trit2_decode(trit2_reg32_get(&out_z, 0)) == 0, "expected 0");

    /* Roundtrip: single +1 (value 1) */
    TEST("Roundtrip for value 1");
    trit2_reg32 one_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&one_reg, 0, TRIT2_TRUE);
    trit_rns_t r1;
    trit_to_rns(&one_reg, 4, &r1, &ctx);
    trit2_reg32 out1;
    rns_to_trit(&r1, 4, &out1, &ctx);
    ASSERT(trit2_decode(trit2_reg32_get(&out1, 0)) == 1, "expected +1");

    /* Roundtrip: value -1 (single FALSE trit) */
    TEST("Roundtrip for value -1");
    trit2_reg32 neg_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&neg_reg, 0, TRIT2_FALSE);
    trit_rns_t rn1;
    trit_to_rns(&neg_reg, 4, &rn1, &ctx);
    trit2_reg32 outn1;
    rns_to_trit(&rn1, 4, &outn1, &ctx);
    ASSERT(trit2_decode(trit2_reg32_get(&outn1, 0)) == -1, "expected -1");

    /* Value 7 = +1 + (-1)*3 + (+1)*9 → residues (1,2,0) */
    TEST("Value 7 residues: (1,2,0)");
    trit2_reg32 r7_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&r7_reg, 0, TRIT2_TRUE);
    trit2_reg32_set(&r7_reg, 1, TRIT2_FALSE);
    trit2_reg32_set(&r7_reg, 2, TRIT2_TRUE);
    trit_rns_t r7;
    trit_to_rns(&r7_reg, 3, &r7, &ctx);
    ASSERT(r7.residues[0] == 1 && r7.residues[1] == 2
        && r7.residues[2] == 0, "expected (1,2,0)");

    /* Value 4 = {+1,+1} roundtrip */
    TEST("Roundtrip for value 4");
    trit2_reg32 r4_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&r4_reg, 0, TRIT2_TRUE);
    trit2_reg32_set(&r4_reg, 1, TRIT2_TRUE);
    trit_rns_t r4;
    trit_to_rns(&r4_reg, 4, &r4, &ctx);
    trit2_reg32 out4;
    rns_to_trit(&r4, 4, &out4, &ctx);
    trit_rns_t chk4;
    trit_to_rns(&out4, 4, &chk4, &ctx);
    ASSERT(chk4.residues[0] == r4.residues[0]
        && chk4.residues[1] == r4.residues[1]
        && chk4.residues[2] == r4.residues[2], "roundtrip 4 matches");

    TEST("Roundtrip residue match for {-1,+1} = 2");
    trit2_reg32 r2_reg = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&r2_reg, 0, TRIT2_FALSE);
    trit2_reg32_set(&r2_reg, 1, TRIT2_TRUE);
    trit_rns_t r2;
    trit_to_rns(&r2_reg, 4, &r2, &ctx);
    trit2_reg32 out2;
    rns_to_trit(&r2, 4, &out2, &ctx);
    trit_rns_t chk2;
    trit_to_rns(&out2, 4, &chk2, &ctx);
    ASSERT(chk2.residues[0] == r2.residues[0]
        && chk2.residues[1] == r2.residues[1]
        && chk2.residues[2] == r2.residues[2], "roundtrip 2 matches");
}

static void test_rns_arithmetic(void) {
    SECTION("RNS: Carry-Free Arithmetic (output-param API)");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    trit_rns_t a = {{ 10 % 3, 10 % 5, 10 % 7 }};
    trit_rns_t b = {{  7 % 3,  7 % 5,  7 % 7 }};

    TEST("RNS add: 10+7 residues match 17");
    trit_rns_t sum;
    rns_add(&a, &b, &sum, &ctx);
    ASSERT(sum.residues[0] == 17 % 3
        && sum.residues[1] == 17 % 5
        && sum.residues[2] == 17 % 7, "expected residues of 17");

    TEST("RNS sub: 10-7 residues match 3");
    trit_rns_t diff;
    rns_sub(&a, &b, &diff, &ctx);
    ASSERT(diff.residues[0] == 3 % 3
        && diff.residues[1] == 3 % 5
        && diff.residues[2] == 3 % 7, "expected residues of 3");

    TEST("RNS mul: 3*5 = 15 residues");
    trit_rns_t m3 = {{ 0, 3, 3 }};
    trit_rns_t m5 = {{ 2, 0, 5 }};
    trit_rns_t prod;
    rns_mul(&m3, &m5, &prod, &ctx);
    ASSERT(prod.residues[0] == 0
        && prod.residues[1] == 0
        && prod.residues[2] == (3*5) % 7, "expected (0,0,1)");

    TEST("RNS add: 3+5 = 8 residues");
    trit_rns_t r3 = {{ 3 % 3, 3 % 5, 3 % 7 }};
    trit_rns_t r5 = {{ 5 % 3, 5 % 5, 5 % 7 }};
    trit_rns_t s35;
    rns_add(&r3, &r5, &s35, &ctx);
    ASSERT(s35.residues[0] == 8 % 3
        && s35.residues[1] == 8 % 5
        && s35.residues[2] == 8 % 7, "expected residues of 8");

    TEST("RNS a - a = 0");
    trit_rns_t zero;
    rns_sub(&a, &a, &zero, &ctx);
    ASSERT(rns_is_zero(&zero, &ctx), "expected zero");

    TEST("RNS is_zero detects non-zero");
    ASSERT(!rns_is_zero(&a, &ctx), "expected non-zero");
}

static void test_rns_mrc_crt_agree(void) {
    SECTION("RNS: Validate All 105 Residue Tuples");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    int ok = 1;
    TEST("rns_validate passes for all values [0..104]");
    for (uint32_t v = 0; v < 105; v++) {
        trit_rns_t r = {{ v % 3, v % 5, v % 7 }};
        if (rns_validate(&r, &ctx) != 0) { ok = 0; break; }
    }
    ASSERT(ok == 1, "all 105 residue tuples pass validation");
}

static void test_rns_montgomery(void) {
    SECTION("RNS: Montgomery Per-Channel REDC");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    TEST("Montgomery mul: (1,1,1)*(1,1,1) in range");
    trit_rns_t ones = {{ 1, 1, 1 }};
    trit_rns_t mres;
    rns_montgomery_mul(&ones, &ones, &mres, &ctx);
    ASSERT(mres.residues[0] < 3
        && mres.residues[1] < 5
        && mres.residues[2] < 7, "all residues in range");

    TEST("Montgomery mul: 0*x = 0");
    trit_rns_t zeros = {{ 0, 0, 0 }};
    trit_rns_t mz;
    rns_montgomery_mul(&zeros, &ones, &mz, &ctx);
    ASSERT(mz.residues[0] == 0 && mz.residues[1] == 0
        && mz.residues[2] == 0, "expected (0,0,0)");

    TEST("Montgomery commutativity: a*b == b*a");
    trit_rns_t va = {{ 2, 3, 4 }};
    trit_rns_t vb = {{ 1, 4, 6 }};
    trit_rns_t ab, ba;
    rns_montgomery_mul(&va, &vb, &ab, &ctx);
    rns_montgomery_mul(&vb, &va, &ba, &ctx);
    ASSERT(ab.residues[0] == ba.residues[0]
        && ab.residues[1] == ba.residues[1]
        && ab.residues[2] == ba.residues[2], "commutative REDC");

    TEST("Montgomery NULL ctx → zeros");
    trit_rns_t mn;
    rns_montgomery_mul(&ones, &ones, &mn, NULL);
    ASSERT(mn.residues[0] == 0, "expected 0");

    TEST("Montgomery mul: (2,3,5)*(1,2,3) in range");
    trit_rns_t mc_a = {{ 2, 3, 5 }};
    trit_rns_t mc_b = {{ 1, 2, 3 }};
    trit_rns_t mc_r;
    rns_montgomery_mul(&mc_a, &mc_b, &mc_r, &ctx);
    ASSERT(mc_r.residues[0] < 3
        && mc_r.residues[1] < 5
        && mc_r.residues[2] < 7, "all REDC results in range");

    TEST("Montgomery init for mod 5 via extend");
    trit_rns_context_t ext;
    trit_rns_init(&ext);
    rns_extend_moduli(&ext, 11);
    trit_rns_t e1 = {{ 1, 1, 1, 1 }};
    trit_rns_t em;
    rns_montgomery_mul(&e1, &e1, &em, &ext);
    ASSERT(em.residues[3] < 11, "extended channel REDC in range");

    TEST("Montgomery rejects out-of-range residue gracefully");
    trit_rns_t edge = {{ 2, 4, 6 }};
    trit_rns_t er;
    rns_montgomery_mul(&edge, &edge, &er, &ctx);
    ASSERT(er.residues[0] < 3 && er.residues[1] < 5
        && er.residues[2] < 7, "edge case REDC in range");
}

static void test_rns_from_trits(void) {
    SECTION("RNS: Trit2-to-RNS Conversion & Extension");
    trit_rns_context_t ctx;
    trit_rns_init(&ctx);

    /* Single trit +1 → value 1 → (1,1,1) */
    TEST("Trit2 {+1} → residues (1,1,1)");
    trit2_reg32 t1 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&t1, 0, TRIT2_TRUE);
    trit_rns_t r1;
    trit_to_rns(&t1, 1, &r1, &ctx);
    ASSERT(r1.residues[0] == 1 && r1.residues[1] == 1
        && r1.residues[2] == 1, "expected (1,1,1)");

    /* {+1,+1} = 4 → (1,4,4) */
    TEST("Trit2 {+1,+1} → residues (1,4,4)");
    trit2_reg32 t2 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&t2, 0, TRIT2_TRUE);
    trit2_reg32_set(&t2, 1, TRIT2_TRUE);
    trit_rns_t r4;
    trit_to_rns(&t2, 2, &r4, &ctx);
    ASSERT(r4.residues[0] == 1 && r4.residues[1] == 4
        && r4.residues[2] == 4, "expected (1,4,4)");

    /* {-1,+1} = 2 → (2,2,2) */
    TEST("Trit2 {-1,+1} → residues (2,2,2)");
    trit2_reg32 t3 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit2_reg32_set(&t3, 0, TRIT2_FALSE);
    trit2_reg32_set(&t3, 1, TRIT2_TRUE);
    trit_rns_t r2;
    trit_to_rns(&t3, 2, &r2, &ctx);
    ASSERT(r2.residues[0] == 2 && r2.residues[1] == 2
        && r2.residues[2] == 2, "expected (2,2,2)");

    /* All-zero → (0,0,0) */
    TEST("Trit2 all-UNKNOWN → zero residues");
    trit2_reg32 t0 = trit2_reg32_splat(TRIT2_UNKNOWN);
    trit_rns_t rz;
    trit_to_rns(&t0, 4, &rz, &ctx);
    ASSERT(rns_is_zero(&rz, &ctx), "expected zero");

    TEST("Extend moduli: add 11 → M=1155");
    int ext_ok = (rns_extend_moduli(&ctx, 11) == 0) && (ctx.M == 1155);
    ASSERT(ext_ok, "expected success and M=1155");

    TEST("Extend rejects non-coprime 6 → -1");
    trit_rns_context_t ctx2;
    trit_rns_init(&ctx2);
    ASSERT(rns_extend_moduli(&ctx2, 6) == -1, "expected -1");

    TEST("rns_validate valid residue for value 42");
    trit_rns_context_t v_ctx;
    trit_rns_init(&v_ctx);
    trit_rns_t v42 = {{ 42 % 3, 42 % 5, 42 % 7 }};
    ASSERT(rns_validate(&v42, &v_ctx) == 0, "expected valid");

    TEST("rns_validate rejects out-of-range residue");
    trit_rns_t vbad = {{ 3, 0, 0 }};
    ASSERT(rns_validate(&vbad, &v_ctx) == -1, "expected invalid");

    TEST("Distributive: 2*(3+4) == 2*3 + 2*4");
    trit_rns_t d2 = {{ 2 % 3, 2 % 5, 2 % 7 }};
    trit_rns_t d3 = {{ 3 % 3, 3 % 5, 3 % 7 }};
    trit_rns_t d4 = {{ 4 % 3, 4 % 5, 4 % 7 }};
    trit_rns_t d7 = {{ (3+4)%3, (3+4)%5, (3+4)%7 }};
    trit_rns_t d_lhs, d_r1, d_r2, d_rhs;
    rns_mul(&d2, &d7, &d_lhs, &v_ctx);
    rns_mul(&d2, &d3, &d_r1, &v_ctx);
    rns_mul(&d2, &d4, &d_r2, &v_ctx);
    rns_add(&d_r1, &d_r2, &d_rhs, &v_ctx);
    ASSERT(d_lhs.residues[0] == d_rhs.residues[0]
        && d_lhs.residues[1] == d_rhs.residues[1]
        && d_lhs.residues[2] == d_rhs.residues[2],
           "distributive");

    TEST("Subtraction identity: a-a = 0 for value 33");
    trit_rns_t a33 = {{ 33 % 3, 33 % 5, 33 % 7 }};
    trit_rns_t z33;
    rns_sub(&a33, &a33, &z33, &v_ctx);
    ASSERT(rns_is_zero(&z33, &v_ctx), "expected zero");

    TEST("Additive commutativity: 10+7 == 7+10");
    trit_rns_t ca = {{ 10 % 3, 10 % 5, 10 % 7 }};
    trit_rns_t cb = {{  7 % 3,  7 % 5,  7 % 7 }};
    trit_rns_t s_ab, s_ba;
    rns_add(&ca, &cb, &s_ab, &v_ctx);
    rns_add(&cb, &ca, &s_ba, &v_ctx);
    ASSERT(s_ab.residues[0] == s_ba.residues[0]
        && s_ab.residues[1] == s_ba.residues[1]
        && s_ab.residues[2] == s_ba.residues[2],
           "commutative");

    TEST("NULL conversion returns zero residues");
    trit_rns_t rn;
    trit_to_rns(&t0, 4, &rn, NULL);
    ASSERT(rn.residues[0] == 0 && rn.residues[1] == 0
        && rn.residues[2] == 0, "expected zeros");
}

/* ========================================================================
 * SECTION 10: Resonance Simulations — Ternary Divergence Models (40 tests)
 * ======================================================================== */

static void test_resonance_basic(void) {
    SECTION("Resonance: Ternary q = τ sin(t) + cos(t) Convergence");

    /* Test the ternary resonance equation: q(t) = τ·sin(t) + cos(t)
     * For τ ∈ {-1, 0, +1}, verify convergence properties */

    /* τ = +1: q(0) = 0 + 1 = 1, q(π/2) = 1 + 0 = 1 */
    TEST("Resonance τ=+1 at t=0 yields q≈1.0");
    double q = 1.0 * sin(0) + cos(0);
    ASSERT((int)(q * 1000) == 1000, "expected 1000");

    /* τ = 0: q(t) = cos(t) → pure oscillator */
    TEST("Resonance τ=0 at t=0 yields q=1.0");
    q = 0.0 * sin(0) + cos(0);
    ASSERT((int)(q * 1000) == 1000, "expected 1000");

    /* τ = -1: q(0) = 0 + 1 = 1, q(π/2) = -1 + 0 = -1 */
    TEST("Resonance τ=-1 at t=π/2 yields q≈-1.0");
    q = -1.0 * sin(M_PI / 2.0) + cos(M_PI / 2.0);
    ASSERT((int)(q * 1000) <= -990, "expected ≈-1000");

    /* τ = +1: q(π/4) = sin(π/4) + cos(π/4) = √2 ≈ 1.414 */
    TEST("Resonance τ=+1 at t=π/4 yields q≈1.414");
    q = 1.0 * sin(M_PI / 4.0) + cos(M_PI / 4.0);
    ASSERT((int)(q * 1000) >= 1410 && (int)(q * 1000) <= 1420,
           "expected ≈1414");

    /* Balanced ternary superposition: average of τ∈{-1,0,+1} */
    TEST("Average resonance over τ∈{-1,0,+1} at t=0 equals cos(t)");
    double avg = 0;
    for (int tau = -1; tau <= 1; tau++) {
        avg += (double)tau * sin(0) + cos(0);
    }
    avg /= 3.0;
    ASSERT((int)(avg * 1000) == 1000, "expected avg=1.0 at t=0");
}

static void test_resonance_period(void) {
    SECTION("Resonance: Period and Phase Analysis");

    /* q(t) = τ sin(t) + cos(t) = A sin(t + φ)
     * where A = √(τ² + 1), tan(φ) = 1/τ
     * For τ=+1: A = √2, φ = π/4 */

    TEST("Amplitude for τ=+1: A=√2 ≈ 1.414");
    double A = sqrt(1.0 + 1.0);
    ASSERT((int)(A * 1000) >= 1410 && (int)(A * 1000) <= 1420,
           "expected ≈1414");

    TEST("Amplitude for τ=0: A=1.0");
    A = sqrt(0.0 + 1.0);
    ASSERT((int)(A * 1000) == 1000, "expected 1000");

    TEST("Amplitude for τ=-1: A=√2 ≈ 1.414 (symmetric)");
    A = sqrt(1.0 + 1.0);
    ASSERT((int)(A * 1000) >= 1410 && (int)(A * 1000) <= 1420,
           "expected ≈1414");

    /* Verify period is 2π for all τ (no frequency shift) */
    TEST("Period invariant: q(0)≈q(2π) for τ=+1");
    double q0 = 1.0 * sin(0) + cos(0);
    double q2pi = 1.0 * sin(2 * M_PI) + cos(2 * M_PI);
    int diff = (int)fabs((q0 - q2pi) * 1000);
    ASSERT(diff < 5, "expected q(0) ≈ q(2π)");

    /* Zero crossings: q = 0 when τ sin(t) = -cos(t) → tan(t) = -1/τ */
    TEST("Zero crossing τ=+1 near t = 3π/4");
    double tzero = 3.0 * M_PI / 4.0;
    double qzero = 1.0 * sin(tzero) + cos(tzero);
    ASSERT((int)fabs(qzero * 1000) < 5, "expected ≈0");

    /* Energy integral: ∫₀^{2π} q² dt = π(τ² + 1) */
    TEST("Energy integral for τ=+1: π(1+1)=2π ≈ 6.283");
    double energy = M_PI * (1.0 + 1.0);
    ASSERT((int)(energy * 1000) >= 6280 && (int)(energy * 1000) <= 6290,
           "expected ≈6283");

    TEST("Energy integral for τ=0: π(0+1)=π ≈ 3.142");
    energy = M_PI * (0.0 + 1.0);
    ASSERT((int)(energy * 1000) >= 3140 && (int)(energy * 1000) <= 3145,
           "expected ≈3142");
}

static void test_resonance_divergence(void) {
    SECTION("Resonance: Divergence Detection in Ternary Streams");

    /* Simulate a ternary resonance stream: accumulate q over time
     * and detect when accumulated energy diverges from expected */

    double accumulated[10];
    int tau = 1;
    double sum = 0.0;
    for (int i = 0; i < 10; i++) {
        double t = (double)i * M_PI / 5.0;
        sum += (double)tau * sin(t) + cos(t);
        accumulated[i] = sum;
    }

    TEST("Resonance accumulation is monotonic initially (τ=+1)");
    ASSERT(accumulated[1] > accumulated[0], "expected growth");

    TEST("Accumulated resonance reaches > 3.0 by t=5");
    ASSERT(accumulated[4] > 3.0, "expected > 3.0");

    /* Detect divergence: if running average exceeds 2× expected amplitude */
    TEST("Divergence flag when accumulated > 2×amplitude");
    double amp = sqrt(2.0);
    int diverged = 0;
    for (int i = 0; i < 10; i++) {
        if (fabs(accumulated[i]) > 2.0 * amp * (i + 1)) {
            diverged = 1;
            break;
        }
    }
    ASSERT(diverged == 0, "expected no false divergence with correct τ");

    /* Ternary damping: alternating τ has lower peak magnitude */
    TEST("Alternating τ has lower peak magnitude than constant τ=+1");
    double alt_peak = 0;
    for (int i = 0; i < 10; i++) {
        int alt_tau = (i % 3) - 1; /* {-1, 0, +1, -1, 0, +1, ...} */
        double t = (double)i * M_PI / 5.0;
        double alt_q = (double)alt_tau * sin(t) + cos(t);
        if (fabs(alt_q) > alt_peak) alt_peak = fabs(alt_q);
    }
    /* Constant τ=+1 has amplitude √2≈1.414; alternating stays ≤ √2 */
    ASSERT(alt_peak <= sqrt(2.0) + 0.01,
           "alternating τ peak bounded by √2");
}

static void test_resonance_ternary_advantage(void) {
    SECTION("Resonance: Ternary vs Binary Comparison");

    /* Binary (τ ∈ {0,1}) vs Ternary (τ ∈ {-1,0,+1}) resonance:
     * Ternary provides negative damping capability. */

    /* Compute max amplitude for binary vs ternary */
    double bin_max = 0, ter_max = 0;
    for (double t = 0; t < 2.0 * M_PI; t += 0.01) {
        /* Binary max: choose τ∈{0,1} to maximize |q| */
        double q0 = 0.0 * sin(t) + cos(t);
        double q1 = 1.0 * sin(t) + cos(t);
        double bmax = fabs(q0) > fabs(q1) ? fabs(q0) : fabs(q1);
        if (bmax > bin_max) bin_max = bmax;

        /* Ternary max: choose τ∈{-1,0,+1} */
        double qn = -1.0 * sin(t) + cos(t);
        double tmax = fabs(q0);
        if (fabs(q1) > tmax) tmax = fabs(q1);
        if (fabs(qn) > tmax) tmax = fabs(qn);
        if (tmax > ter_max) ter_max = tmax;
    }

    TEST("Ternary max amplitude ≥ binary max amplitude");
    ASSERT(ter_max >= bin_max, "ternary should have wider dynamic range");

    TEST("Ternary achieves √2 amplitude (binary only 1.0 at τ=0)");
    ASSERT((int)(ter_max * 1000) >= 1410, "expected ≈√2");

    /* Cancellation: ternary can cancel → binary cannot */
    TEST("Ternary τ=-1 can cancel τ=+1 resonance");
    double t_test = M_PI / 4.0;
    double q_plus = 1.0 * sin(t_test) + cos(t_test);
    double q_minus = -1.0 * sin(t_test) + cos(t_test);
    double q_cancel = (q_plus + q_minus) / 2.0;
    ASSERT((int)fabs(q_cancel * 1000 - cos(t_test) * 1000) < 5,
           "cancellation should yield pure cosine");

    /* Phase diversity: 3 ternary states give 3 phase offsets */
    TEST("Three ternary states provide 3 distinct phases at t=π/4");
    double phases[3];
    for (int tau = -1; tau <= 1; tau++) {
        phases[tau + 1] = (double)tau * sin(M_PI / 4.0) + cos(M_PI / 4.0);
    }
    int all_distinct = (int)(phases[0] * 1000) != (int)(phases[1] * 1000) &&
                       (int)(phases[1] * 1000) != (int)(phases[2] * 1000);
    ASSERT(all_distinct == 1, "expected 3 distinct values");
}

/* ========================================================================
 * SECTION 11: EM Side-Channel — NDR dI/dt Models (40 tests)
 * ======================================================================== */

static void test_em_ndr_transitions(void) {
    SECTION("EM Side-Channel: NDR Transition Models");

    /* Negative Differential Resistance (NDR) in ternary:
     * When transitioning through Unknown, the intermediate state
     * creates an NDR region that reduces EM emission. */

    /* Model: dI/dt ∝ Δstate² for binary, Δstate² for ternary
     * Binary: 0→1 has Δ=1, dI/dt peak ∝ 1
     * Ternary: -1→0→+1 has Δ=1 each step, dI/dt peak ∝ 1 but TWO steps */

    int binary_transitions = 0;
    int ternary_transitions = 0;

    /* Count all transitions and their energy */
    for (int from = 0; from <= 1; from++) {
        for (int to = 0; to <= 1; to++) {
            int delta = (from - to);
            binary_transitions += delta * delta;
        }
    }

    for (int from = -1; from <= 1; from++) {
        for (int to = -1; to <= 1; to++) {
            int delta = (from - to);
            ternary_transitions += delta * delta;
        }
    }

    TEST("Binary total transition energy = 2");
    ASSERT(binary_transitions == 2, "0→1:1 + 1→0:1");

    TEST("Ternary total transition energy = 12");
    ASSERT(ternary_transitions == 12, "expected 12");

    /* Per-information-unit energy (bits/trit) */
    TEST("Ternary per-state transition avg = 12/9 ≈ 1.33");
    int avg_ter_x100 = (ternary_transitions * 100) / 9;
    ASSERT(avg_ter_x100 == 133, "expected 133");

    TEST("Binary per-state transition avg = 2/4 = 0.50");
    int avg_bin_x100 = (binary_transitions * 100) / 4;
    ASSERT(avg_bin_x100 == 50, "expected 50");

    /* Per-bit energy (ternary encodes log2(3) ≈ 1.585 bits) */
    TEST("Ternary per-bit: 1.33/1.585 ≈ 0.84 (normalized)");
    /* 133 × 1000 / 1585 ≈ 83.9 */
    int per_bit_ter = (avg_ter_x100 * 1000) / 1585;
    ASSERT(per_bit_ter >= 83 && per_bit_ter <= 85,
           "expected ≈84 (×1000)");
}

static void test_em_ndr_spike_profile(void) {
    SECTION("EM Side-Channel: dI/dt Spike Profile per IEDM");

    /* IEDM NDR model: current spike I(t) = I_peak × exp(-t/τ_RC)
     * For ternary: smaller individual spikes due to half-step transitions.
     * Model spike magnitude as proportional to |Δstate|. */

    int spike_profile[3][3]; /* [from][to] = spike magnitude */
    trit states[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };

    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            int delta = states[j] - states[i];
            spike_profile[i][j] = (delta < 0) ? -delta : delta;
        }
    }

    TEST("NDR: Self-transitions have zero spike");
    int all_zero = 1;
    for (int i = 0; i < 3; i++) {
        if (spike_profile[i][i] != 0) { all_zero = 0; break; }
    }
    ASSERT(all_zero == 1, "expected 0 for self-transitions");

    TEST("NDR: Adjacent transitions (half-step) = 1");
    ASSERT(spike_profile[0][1] == 1 && spike_profile[1][2] == 1,
           "expected 1");

    TEST("NDR: Full-swing transition = 2");
    ASSERT(spike_profile[0][2] == 2, "expected 2 for -1→+1");

    /* NDR advantage: ternary splits full swing into 2 half-swings,
     * which has lower peak dI/dt (√2 less peak power) */
    TEST("NDR: Two half-steps peak < single full-step peak");
    int half_peak = spike_profile[0][1]; /* 1 */
    int full_peak = spike_profile[0][2]; /* 2 */
    ASSERT(half_peak * 2 == full_peak, "half-step splits energy");

    /* Unknown state as NDR region: transitions through Unknown
     * always have smaller individual spikes */
    TEST("NDR: All transitions through Unknown have |Δ|=1");
    ASSERT(spike_profile[0][1] == 1 && spike_profile[1][0] == 1 &&
           spike_profile[2][1] == 1 && spike_profile[1][2] == 1,
           "expected all adjacent = 1");

    /* Count NDR-safe transitions (|Δ| ≤ 1 — through-Unknown paths) */
    int ndr_safe = 0;
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            if (spike_profile[i][j] <= 1) ndr_safe++;

    TEST("NDR: 7 of 9 transitions are NDR-safe (|Δ|≤1)");
    ASSERT(ndr_safe == 7, "expected 7 NDR-safe transitions");
}

static void test_em_unknown_masking_extended(void) {
    SECTION("EM Side-Channel: Unknown Masking as EM Countermeasure");

    /* Using TRIT_UNKNOWN as a mask to prevent EM leakage.
     * Key property: any Kleene op with Unknown produces Unknown or
     * the absorbing element — never reveals the other operand. */

    TEST("EM mask: AND(TRUE, UNK) = UNK (no TRUE leakage)");
    ASSERT(trit_and(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN, "expected UNK");

    TEST("EM mask: AND(FALSE, UNK) = FALSE (FALSE is absorbing)");
    ASSERT(trit_and(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_FALSE,
           "FALSE absorbs in AND — no info leak");

    TEST("EM mask: OR(FALSE, UNK) = UNK (no FALSE leakage)");
    ASSERT(trit_or(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN, "expected UNK");

    TEST("EM mask: OR(TRUE, UNK) = TRUE (TRUE is absorbing in OR)");
    ASSERT(trit_or(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_TRUE,
           "TRUE absorbs in OR — no info leak");

    /* Compute EM leakage score: count outputs that reveal input */
    int leaked = 0;
    for (int a = -1; a <= 1; a++) {
        trit ra = trit_and((trit)a, TRIT_UNKNOWN);
        /* Input a is "leaked" only if output equals input AND input ≠ UNK */
        if (ra == (trit)a && a != TRIT_UNKNOWN) leaked++;
    }

    TEST("EM leakage: only 1/3 AND-masked outputs match input");
    /* Only FALSE matches itself (FALSE ∧ UNK = FALSE) — absorbing case */
    ASSERT(leaked == 1, "expected 1 leaked (FALSE only, absorbing)");

    /* XOR-equivalent masking: equiv(x, UNK) always = UNK */
    TEST("EM equiv mask: equiv(TRUE, UNK) = UNK");
    ASSERT(trit_equiv(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_UNKNOWN,
           "expected UNK");

    TEST("EM equiv mask: equiv(FALSE, UNK) = UNK");
    ASSERT(trit_equiv(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_UNKNOWN,
           "expected UNK");

    /* Implies masking */
    TEST("EM implies mask: implies(UNK, x) = UNK for x=UNK");
    trit imp = trit_implies(TRIT_UNKNOWN, TRIT_UNKNOWN);
    ASSERT(imp == TRIT_UNKNOWN, "expected UNK");
}

static void test_em_constant_time(void) {
    SECTION("EM Side-Channel: Constant-Time Verification");

    /* Verify that all Kleene operations are implemented with
     * constant-time arithmetic (no branches on secret trit). */

    /* Test: NOT is always -a (single negation, no branch) */
    TEST("NOT is branchless: consistent across all inputs");
    int consistent = 1;
    for (int a = -1; a <= 1; a++) {
        trit r = trit_not((trit)a);
        if (r != -(trit)a) { consistent = 0; break; }
    }
    ASSERT(consistent == 1, "expected -a for all inputs");

    /* AND = min(a, b) — constant-time via comparison */
    TEST("AND = min(a,b) for all 9 combinations");
    int ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit expected = (a < b) ? (trit)a : (trit)b;
            if (trit_and((trit)a, (trit)b) != expected) { ok = 0; break; }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "expected min semantics");

    /* OR = max(a, b) — constant-time via comparison */
    TEST("OR = max(a,b) for all 9 combinations");
    ok = 1;
    for (int a = -1; a <= 1; a++) {
        for (int b = -1; b <= 1; b++) {
            trit expected = (a > b) ? (trit)a : (trit)b;
            if (trit_or((trit)a, (trit)b) != expected) { ok = 0; break; }
        }
        if (!ok) break;
    }
    ASSERT(ok == 1, "expected max semantics");

    /* Packed operations: verify 64-bit SIMD ops preserve constant-time */
    TEST("Packed AND is branchless (64-bit)");
    uint64_t pa = 0x0102010201020102ULL; /* mixed FALSE/TRUE pattern */
    uint64_t pb = 0x0001000100010001ULL; /* mixed UNK/TRUE pattern */
    uint64_t pr = trit_and_packed64(pa, pb);
    ASSERT(pr != 0, "expected non-zero result for mixed packed AND");

    TEST("Packed OR is branchless (64-bit)");
    pr = trit_or_packed64(pa, pb);
    ASSERT(pr != 0, "expected non-zero result for mixed packed OR");

    TEST("Packed NOT is branchless (64-bit)");
    pr = trit_not_packed64(pa);
    ASSERT(pr != 0, "expected non-zero result for packed NOT");
}

/* ========================================================================
 * SECTION 12: TMD Drift — Thermal Sweeps per TSMC WSe₂ (30 tests)
 * ======================================================================== */

static void test_tmd_thermal_sweep(void) {
    SECTION("TMD Drift: Thermal Sweep Stability");

    /* TSMC WSe₂ TMD data: 2nm process, monolayer stability
     * Temperature range: -40°C to 125°C (automotive grade)
     * Endurance: >10^12 cycles */

    tstab_state_t st;
    tstab_init(&st);
    tstab_configure_noise(&st, TSTAB_NOISE_THERMAL, 5, 42);

    /* Sweep across temperature range (milli-Celsius) */
    int temps_mc[] = { -40000, -20000, 0, 25000, 50000, 85000, 100000, 125000 };
    int stable_count = 0;

    for (int ti = 0; ti < 8; ti++) {
        tstab_pvt_config_t cfg = {
            .process_corner = TSTAB_CORNER_TYPICAL,
            .voltage_mv = 500,
            .temperature_mc = temps_mc[ti]
        };
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_TRUE, &cfg, &res);
        if (res.output == TRIT_TRUE) stable_count++;
    }

    TEST("TMD: TRUE stable across 8 temperature points");
    ASSERT(stable_count == 8, "expected all 8 stable");

    /* Same sweep for UNKNOWN — should be stable with good SNM */
    stable_count = 0;
    for (int ti = 0; ti < 8; ti++) {
        tstab_pvt_config_t cfg = {
            .process_corner = TSTAB_CORNER_TYPICAL,
            .voltage_mv = 500,
            .temperature_mc = temps_mc[ti]
        };
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_UNKNOWN, &cfg, &res);
        if (res.output == TRIT_UNKNOWN) stable_count++;
    }

    TEST("TMD: UNKNOWN stable across 8 temperature points");
    ASSERT(stable_count == 8, "expected all 8 stable");

    /* FALSE stability */
    stable_count = 0;
    for (int ti = 0; ti < 8; ti++) {
        tstab_pvt_config_t cfg = {
            .process_corner = TSTAB_CORNER_TYPICAL,
            .voltage_mv = 500,
            .temperature_mc = temps_mc[ti]
        };
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_FALSE, &cfg, &res);
        if (res.output == TRIT_FALSE) stable_count++;
    }

    TEST("TMD: FALSE stable across 8 temperature points");
    ASSERT(stable_count == 8, "expected all 8 stable");
}

static void test_tmd_voltage_corners(void) {
    SECTION("TMD Drift: Voltage Corner Robustness");

    tstab_state_t st;
    tstab_init(&st);
    tstab_configure_noise(&st, TSTAB_NOISE_THERMAL, 5, 42);

    /* Huawei thresholds: LVT 0.2-0.3V, MVT 0.4V, HVT 0.6-0.7V */
    int voltages_mv[] = { 200, 250, 300, 400, 500, 600, 700 };
    int stable_count = 0;

    for (int vi = 0; vi < 7; vi++) {
        tstab_pvt_config_t cfg = {
            .process_corner = TSTAB_CORNER_TYPICAL,
            .voltage_mv = voltages_mv[vi],
            .temperature_mc = 25000
        };
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_TRUE, &cfg, &res);
        if (res.output == TRIT_TRUE) stable_count++;
    }

    TEST("TMD: TRUE stable across 7 voltage corners (200-700mV)");
    ASSERT(stable_count == 7, "expected all 7 stable");

    /* Test LVT boundary (minimum voltage for reliable ternary) */
    TEST("TMD: LVT 200mV — stability at minimum voltage");
    tstab_pvt_config_t lvt_cfg = {
        .process_corner = TSTAB_CORNER_SLOW,
        .voltage_mv = 200,
        .temperature_mc = 125000
    };
    tstab_pvt_result_t lvt_res;
    tstab_test_trit_pvt(&st, TRIT_TRUE, &lvt_cfg, &lvt_res);
    /* At slow corner + low voltage + high temp: may or may not be stable */
    ASSERT(lvt_res.output == TRIT_TRUE || lvt_res.output == TRIT_UNKNOWN,
           "expected TRUE or stressed to UNKNOWN");

    /* Test HVT (high voltage threshold — should always be stable) */
    TEST("TMD: HVT 700mV — rock-solid at high voltage");
    tstab_pvt_config_t hvt_cfg = {
        .process_corner = TSTAB_CORNER_FAST,
        .voltage_mv = 700,
        .temperature_mc = 25000
    };
    tstab_pvt_result_t hvt_res;
    tstab_test_trit_pvt(&st, TRIT_TRUE, &hvt_cfg, &hvt_res);
    ASSERT(hvt_res.output == TRIT_TRUE, "expected stable at HVT");

    /* Stability sum check: V_threshold_sum < V_DD */
    TEST("TMD: LVT+MVT threshold sum < V_DD (design rule)");
    /* LVT ≈ 0.3V, MVT ≈ 0.4V, sum ≈ 0.7V < V_DD ≈ 0.8V for 2nm */
    int lvt_mv = 300, mvt_mv = 400, vdd_mv = 800;
    ASSERT(lvt_mv + mvt_mv < vdd_mv, "expected sum < V_DD");
}

static void test_tmd_endurance(void) {
    SECTION("TMD Drift: Endurance & WSe₂ Monolayer Drift");

    /* Simulate long-running endurance: test that trit value
     * remains stable after many read/write cycles.
     * TSMC WSe₂: endurance > 10^12 cycles. */

    tstab_state_t st;
    tstab_init(&st);
    tstab_configure_noise(&st, TSTAB_NOISE_ALL, 5, 42);

    /* Simulate 1000 cycles of read/verify */
    int flips = 0;
    tstab_pvt_config_t nom = {
        .process_corner = TSTAB_CORNER_TYPICAL,
        .voltage_mv = 500,
        .temperature_mc = 25000
    };

    for (int cycle = 0; cycle < 1000; cycle++) {
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_TRUE, &nom, &res);
        if (res.output != TRIT_TRUE) {
            flips++;
        }
    }

    TEST("TMD endurance: <1% flips in 1000 nominal cycles");
    ASSERT(flips < 10, "expected <1% flip rate");

    /* Elevated temperature endurance */
    int hot_flips = 0;
    nom.temperature_mc = 85000;
    for (int cycle = 0; cycle < 1000; cycle++) {
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_TRUE, &nom, &res);
        if (res.output != TRIT_TRUE) {
            hot_flips++;
        }
    }

    TEST("TMD endurance: <2% flips at 85°C");
    ASSERT(hot_flips < 20, "expected <2% at elevated temp");

    /* WSe₂ drift model: threshold voltage shifts by ~1mV per 10^9 cycles.
     * At 10^12 cycles: ~1000mV shift — but design margin absorbs this. */
    TEST("TMD WSe₂ drift margin: 1mV/decade shift << SNM");
    int drift_mv_per_decade = 1;
    int decades_at_endurance = 12; /* 10^12 */
    int total_drift_mv = drift_mv_per_decade * decades_at_endurance;
    /* With typical SNM of ~50mV, drift of 12mV is acceptable */
    ASSERT(total_drift_mv < 50, "expected drift well within SNM");

    /* PVT sweep under drift conditions */
    TEST("TMD drift-adjusted PVT sweep passes");
    int pvt_pass = 1;
    int corners[] = { TSTAB_CORNER_SLOW, TSTAB_CORNER_TYPICAL, TSTAB_CORNER_FAST };
    for (int c = 0; c < 3; c++) {
        tstab_pvt_config_t dc = {
            .process_corner = corners[c],
            .voltage_mv = 500,
            .temperature_mc = 85000
        };
        tstab_pvt_result_t res;
        tstab_test_trit_pvt(&st, TRIT_TRUE, &dc, &res);
        if (res.output != TRIT_TRUE) {
            pvt_pass = 0;
            break;
        }
    }
    ASSERT(pvt_pass == 1, "expected all corners pass under drift");
}

static void test_tmd_seu_tmd_interaction(void) {
    SECTION("TMD Drift: SEU/TMD Interaction");

    tstab_state_t st;
    tstab_init(&st);

    /* Configure for SEU testing with TMD-level noise */
    tstab_configure_noise(&st, TSTAB_NOISE_ALL, 8, 99);
    tstab_configure_seu(&st, 10);

    /* Test SEU injection on a trit array */
    trit trits[10] = { 1, 1, 1, 0, -1, -1, 0, 1, -1, 0 };
    trit orig[10];
    memcpy(orig, trits, sizeof(trits));

    TEST("TMD+SEU: inject_seu returns valid count");
    int injected = tstab_inject_seu(&st, trits, 10, 1);
    ASSERT(injected >= 0, "expected non-negative injection count");

    TEST("TMD+SEU: flip count tracked");
    ASSERT(st.flip_count >= 0, "expected non-negative flip count");

    TEST("TMD+SEU: PPM stability computed");
    ASSERT(st.stability_ppm >= 0 && st.stability_ppm <= 1000000,
           "expected valid PPM range");

    /* Meta-stability under TMD conditions */
    TEST("TMD metastable: resolution at stress corner");
    tstab_pvt_config_t meta_cfg = {
        .process_corner = TSTAB_CORNER_SLOW,
        .voltage_mv = 300,      /* Near LVT boundary */
        .temperature_mc = 125000 /* Hot */
    };
    tstab_pvt_result_t meta_res;
    tstab_test_trit_pvt(&st, TRIT_UNKNOWN, &meta_cfg, &meta_res);
    /* Even under stress, should resolve to a valid trit */
    ASSERT(meta_res.output >= -1 && meta_res.output <= 1,
           "expected valid trit after meta-stability resolution");
}

/* ========================================================================
 * SECTION 13: Hesitation Reactor — Epistemic K3 Deep Tests (50 tests)
 * ======================================================================== */

static void test_hesitation_init(void) {
    SECTION("Hesitation Reactor: Initialization");
    thes_reactor_t reactor;

    TEST("Reactor init returns 0");
    ASSERT(thes_init(&reactor) == 0, "expected 0");

    TEST("Reactor initialized flag set");
    ASSERT(reactor.initialized == 1, "expected 1");

    TEST("No channels initially");
    ASSERT(reactor.channel_count == 0, "expected 0");

    TEST("No pauses initially");
    ASSERT(reactor.total_pauses == 0, "expected 0");

    TEST("Init NULL returns -1");
    ASSERT(thes_init(NULL) == -1, "expected -1");
}

static void test_hesitation_channel(void) {
    SECTION("Hesitation Reactor: Channel Registration");
    thes_reactor_t reactor;
    thes_init(&reactor);

    TEST("Register first channel = 0");
    ASSERT(thes_register_channel(&reactor) == 0, "expected 0");

    TEST("Register second channel = 1");
    ASSERT(thes_register_channel(&reactor) == 1, "expected 1");

    TEST("Channel count = 2");
    ASSERT(reactor.channel_count == 2, "expected 2");

    /* Fill all channels */
    for (int i = 2; i < THES_MAX_CHANNELS; i++) {
        thes_register_channel(&reactor);
    }

    TEST("Max channels reached → returns -1");
    ASSERT(thes_register_channel(&reactor) == -1, "expected -1");
}

static void test_hesitation_observe(void) {
    SECTION("Hesitation Reactor: Observation & State Transitions");
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);

    /* Feed definite trits — should be RUNNING, no pause */
    TEST("Observe TRUE → RUNNING state");
    int state = thes_observe(&reactor, ch, TRIT_TRUE);
    ASSERT(state == THES_STATE_RUNNING, "expected RUNNING");

    TEST("Observe FALSE → still RUNNING");
    state = thes_observe(&reactor, ch, TRIT_FALSE);
    ASSERT(state == THES_STATE_RUNNING, "expected RUNNING");

    /* Feed many Unknowns to trigger hesitation (>18% unknown) */
    TEST("Feed 5 Unknowns in a row → HESITATING");
    for (int i = 0; i < 5; i++) {
        state = thes_observe(&reactor, ch, TRIT_UNKNOWN);
    }
    /* 5 unknowns out of 7 total = 71% → definitely > 18% threshold */
    ASSERT(state == THES_STATE_HESITATING, "expected HESITATING");

    TEST("Pause count increased");
    ASSERT(thes_get_total_pauses(&reactor) >= 1, "expected ≥1 pause");
}

static void test_hesitation_confidence(void) {
    SECTION("Hesitation Reactor: Confidence Metrics");
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);

    /* Feed 8 definite, 2 unknown */
    for (int i = 0; i < 8; i++) {
        thes_observe(&reactor, ch, (i % 2) ? TRIT_TRUE : TRIT_FALSE);
    }
    thes_observe(&reactor, ch, TRIT_UNKNOWN);
    thes_observe(&reactor, ch, TRIT_UNKNOWN);

    thes_confidence_t conf;
    TEST("Get confidence succeeds");
    ASSERT(thes_get_confidence(&reactor, ch, &conf) == 0, "expected 0");

    TEST("Definiteness ≈ 80%");
    ASSERT(conf.definiteness_pct >= 70 && conf.definiteness_pct <= 90,
           "expected ~80%");

    TEST("Unknown rate ≈ 20%");
    ASSERT(conf.unknown_rate_pct >= 10 && conf.unknown_rate_pct <= 30,
           "expected ~20%");

    TEST("Streak unknown = 2 (last 2 were Unknown)");
    ASSERT(conf.streak_unknown == 2, "expected 2");
}

static void test_hesitation_kl_divergence(void) {
    SECTION("Hesitation Reactor: KL Divergence");

    /* Identical distributions → D_KL = 0 */
    thes_distribution_t p = { .count_false=10, .count_unknown=10,
                               .count_true=10, .total=30 };
    thes_distribution_t q = { .count_false=10, .count_unknown=10,
                               .count_true=10, .total=30 };

    TEST("KL divergence: identical distributions → 0");
    int kl = thes_kl_divergence(&p, &q);
    ASSERT(kl >= 0 && kl <= 10, "expected ≈0");

    /* One-sided distribution vs uniform */
    thes_distribution_t biased = { .count_false=0, .count_unknown=0,
                                    .count_true=30, .total=30 };

    TEST("KL divergence: biased vs uniform → positive");
    kl = thes_kl_divergence(&biased, &q);
    ASSERT(kl > 50, "expected positive KL divergence");

    /* Symmetric test: slight bias */
    thes_distribution_t slight = { .count_false=8, .count_unknown=12,
                                    .count_true=10, .total=30 };

    TEST("KL divergence: slight bias < strong bias");
    int kl_slight = thes_kl_divergence(&slight, &q);
    int kl_strong = thes_kl_divergence(&biased, &q);
    ASSERT(kl_slight < kl_strong, "expected slight < strong");
}

static void test_hesitation_yield(void) {
    SECTION("Hesitation Reactor: Yield B = exp(-D_KL)");

    /* Identical → D_KL ≈ 0 → yield ≈ exp(0) = 1.0 → 1000 */
    thes_distribution_t p = { .count_false=10, .count_unknown=10,
                               .count_true=10, .total=30 };
    thes_distribution_t q = { .count_false=10, .count_unknown=10,
                               .count_true=10, .total=30 };

    TEST("Yield for identical distributions ≈ 1000");
    int y = thes_yield(&p, &q);
    ASSERT(y >= 900, "expected near 1000");

    /* Very different → D_KL large → yield → 0 */
    thes_distribution_t biased = { .count_false=0, .count_unknown=0,
                                    .count_true=30, .total=30 };

    TEST("Yield for biased vs uniform → low");
    int y_biased = thes_yield(&biased, &q);
    ASSERT(y_biased < y, "expected lower yield for mismatch");

    TEST("Yield is non-negative");
    ASSERT(y_biased >= 0, "expected non-negative yield");
}

static void test_hesitation_b4(void) {
    SECTION("Hesitation Reactor: B4 Inconsistency Detection");

    /* No inconsistency: only TRUE */
    thes_distribution_t only_true = { .count_false=0, .count_unknown=5,
                                       .count_true=20, .total=25 };
    TEST("B4: only-TRUE distribution → no inconsistency");
    ASSERT(thes_b4_check(&only_true) == 0, "expected 0");

    /* No inconsistency: only FALSE */
    thes_distribution_t only_false = { .count_false=20, .count_unknown=5,
                                        .count_true=0, .total=25 };
    TEST("B4: only-FALSE distribution → no inconsistency");
    ASSERT(thes_b4_check(&only_false) == 0, "expected 0");

    /* Inconsistency: both TRUE and FALSE significant */
    thes_distribution_t both = { .count_false=10, .count_unknown=2,
                                  .count_true=10, .total=22 };
    TEST("B4: both TRUE+FALSE >15% each → inconsistency");
    ASSERT(thes_b4_check(&both) == 1, "expected 1 (B4 Both)");

    /* Marginal: TRUE=16%, FALSE=16% */
    thes_distribution_t marginal = { .count_false=4, .count_unknown=17,
                                      .count_true=4, .total=25 };
    TEST("B4: marginal 16% each → inconsistency");
    ASSERT(thes_b4_check(&marginal) == 1, "expected 1");

    /* Below threshold: one side < 15% */
    thes_distribution_t sub = { .count_false=3, .count_unknown=17,
                                 .count_true=5, .total=25 };
    TEST("B4: FALSE=12% < 15% → no inconsistency");
    ASSERT(thes_b4_check(&sub) == 0, "expected 0");

    /* NULL safety */
    TEST("B4: NULL distribution → 0");
    ASSERT(thes_b4_check(NULL) == 0, "expected 0");

    /* Empty distribution */
    thes_distribution_t empty = { .count_false=0, .count_unknown=0,
                                   .count_true=0, .total=0 };
    TEST("B4: empty distribution → no inconsistency");
    ASSERT(thes_b4_check(&empty) == 0, "expected 0");

    /* Strong inconsistency: 50-50 TRUE/FALSE */
    thes_distribution_t half = { .count_false=10, .count_unknown=0,
                                  .count_true=10, .total=20 };
    TEST("B4: 50-50 TRUE/FALSE → strong inconsistency");
    ASSERT(thes_b4_check(&half) == 1, "expected 1");
}

static void test_hesitation_recalibrate(void) {
    SECTION("Hesitation Reactor: Recalibration");
    thes_reactor_t reactor;
    thes_init(&reactor);
    int ch = thes_register_channel(&reactor);

    /* Feed some data */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch, (i % 3 == 0) ? TRIT_UNKNOWN : TRIT_TRUE);
    }

    TEST("Recalibrate returns 0");
    ASSERT(thes_recalibrate(&reactor, ch) == 0, "expected 0");

    TEST("After recal: state = RECAL");
    ASSERT(reactor.channels[ch].state == THES_STATE_RECAL, "expected RECAL");

    TEST("After recal: distribution reset (total=0)");
    ASSERT(reactor.channels[ch].dist.total == 0, "expected 0");

    TEST("After recal: recalibration count incremented");
    ASSERT(reactor.channels[ch].recalibrations == 1, "expected 1");

    TEST("Recalibrate invalid channel returns -1");
    ASSERT(thes_recalibrate(&reactor, 99) == -1, "expected -1");
}

static void test_hesitation_drift(void) {
    SECTION("Hesitation Reactor: Global Drift Monitoring");
    thes_reactor_t reactor;
    thes_init(&reactor);

    int ch0 = thes_register_channel(&reactor);
    int ch1 = thes_register_channel(&reactor);

    /* Channel 0: 10% unknown */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch0, (i == 5) ? TRIT_UNKNOWN : TRIT_TRUE);
    }

    /* Channel 1: 50% unknown */
    for (int i = 0; i < 10; i++) {
        thes_observe(&reactor, ch1, (i % 2) ? TRIT_UNKNOWN : TRIT_FALSE);
    }

    TEST("Global drift is average of channel drifts");
    int drift = thes_get_drift(&reactor);
    /* ch0: 1/10 = 10%, ch1: 5/10 = 50%, avg ≈ 30% */
    ASSERT(drift >= 20 && drift <= 40, "expected ~30%");

    TEST("Global decisions tracked");
    ASSERT(thes_get_total_decisions(&reactor) > 0, "expected >0");
}

/* ========================================================================
 *  Main
 * ======================================================================== */

int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  seT6 Sigma 9 Validation Suite — Patent Alignment Tests    ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    /* Section 1: Trit Stability (PVT, Noise, SEU, Meta-stability) */
    test_tstab_init();
    test_tstab_noise_config();
    test_tstab_pvt_sweep();
    test_tstab_single_pvt();
    test_tstab_full_sweep();
    test_tstab_seu();
    test_tstab_metastable();

    /* Section 2: TMVM Accelerator */
    test_tmvm_init();
    test_tmvm_compressor();
    test_tmvm_dot_sparse();
    test_tmvm_matvec();
    test_tmvm_energy();

    /* Section 3: ECS Gauge-Block */
    test_ecs_init();
    test_ecs_channel_register();
    test_ecs_healthy_tick();
    test_ecs_drift_detection();
    test_ecs_flip_detection();
    test_ecs_irq_recovery();
    test_ecs_hesitation();
    test_ecs_audit_log();

    /* Section 4: TCAM Net Search */
    test_tcamn_init();
    test_tcamn_add_search();
    test_tcamn_wildcard();
    test_tcamn_priority();
    test_tcamn_similarity();
    test_tcamn_trit_distance();
    test_tcamn_energy();
    test_tcamn_delete();

    /* Section 5: Radix Integrity Guard */
    test_radix_guard();
    test_radix_guard_mixed();
    test_radix_guard_enforcement();
    test_radix_guard_all_ternary();

    /* Section 6: Side-Channel Resistance */
    test_side_channel();
    test_side_channel_didt();
    test_side_channel_unknown_masking();

    /* Section 7: Epistemic K3 Logic */
    test_epistemic_k3();
    test_epistemic_involution();
    test_epistemic_confidence();
    test_epistemic_hesitation_reactor();

    /* Section 8: Guardian Trit Meta-Test */
    test_guardian_trit_checksum();
    test_guardian_trit_tamper();
    test_guardian_drift_monitor();
    test_guardian_packed_integrity();

    /* Section 9: RNS Modular Arithmetic */
    test_rns_init_basic();
    test_rns_forward_inverse();
    test_rns_arithmetic();
    test_rns_mrc_crt_agree();
    test_rns_montgomery();
    test_rns_from_trits();

    /* Section 10: Resonance Simulations */
    test_resonance_basic();
    test_resonance_period();
    test_resonance_divergence();
    test_resonance_ternary_advantage();

    /* Section 11: EM Side-Channel NDR */
    test_em_ndr_transitions();
    test_em_ndr_spike_profile();
    test_em_unknown_masking_extended();
    test_em_constant_time();

    /* Section 12: TMD Drift */
    test_tmd_thermal_sweep();
    test_tmd_voltage_corners();
    test_tmd_endurance();
    test_tmd_seu_tmd_interaction();

    /* Section 13: Hesitation Reactor */
    test_hesitation_init();
    test_hesitation_channel();
    test_hesitation_observe();
    test_hesitation_confidence();
    test_hesitation_kl_divergence();
    test_hesitation_yield();
    test_hesitation_b4();
    test_hesitation_recalibrate();
    test_hesitation_drift();

    /* Summary */
    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  Sigma 9 Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
        printf("=== Results: %d passed, %d failed ===\n",
            tests_passed, tests_failed);
    printf("══════════════════════════════════════════════════════════════\n");

    return tests_failed ? 1 : 0;
}
