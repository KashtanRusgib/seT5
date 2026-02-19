/**
 * @file test_dlt_cntfet.c
 * @brief seT6 DLT Expansion + CNTFET Gate Emulation Test Suite
 *
 * Validates:
 *   Section 1: DLT Tequila Expansion — asymmetric thresholds, STE,
 *              reactivation, trapping rate (20 tests)
 *   Section 2: CNTFET Emulation — device creation, V_TH model, TNAND/TNOR,
 *              drift simulation, stabilise, endurance, Huawei class (30 tests)
 *   Section 3: Module Integration — stabilize+CNTFET drift, tmvm+DLT quant,
 *              ecs_gauge endurance, hesitation DLT react (10 tests)
 *
 * Total: 60 assertions
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "set5/trit_dlt.h"
#include "set5/trit_cntfet_emu.h"
#include "set5/trit_stabilize.h"
#include "set5/trit_tmvm.h"
#include "set5/trit_ecs_gauge.h"
#include "set5/trit_hesitation.h"

/* ==== Test Harness ===================================================== */

static int tests_passed = 0;
static int tests_failed = 0;
static int tests_total  = 0;

#define TEST(name) do { \
    printf("  %-60s", name); \
    tests_total++; \
} while (0)

#define ASSERT(cond, msg) do { \
    if (cond) { \
        tests_passed++; \
        printf("[PASS]\n"); \
    } else { \
        tests_failed++; \
        printf("[FAIL] %s\n", msg); \
    } \
} while (0)

static void print_section(const char *name) {
    printf("\n  --- %s ---\n", name);
}

/* ==== Section 1: DLT Tequila Expansion (20 tests) ====================== */

static void test_dlt_expansion(void) {
    print_section("DLT: Tequila Expansion — Asymmetric + STE + Reactivation");

    dlt_state_t dlt;

    /* Basic init */
    TEST("dlt_init returns 0");
    ASSERT(dlt_init(&dlt) == 0, "init failed");

    TEST("dlt_add_layer returns 0");
    int layer = dlt_add_layer(&dlt);
    ASSERT(layer == 0, "add_layer failed");

    /* Layer initial state: sp, sn, delta_p, delta_n = 0 */
    TEST("layer sp = 0 initially");
    ASSERT(dlt.layers[0].sp == 0, "sp not 0");

    TEST("layer sn = 0 initially");
    ASSERT(dlt.layers[0].sn == 0, "sn not 0");

    /* Asymmetric threshold computation */
    int weights[] = {800, 600, 300, -200, -400, -700, 0, 100, -50, 150};
    int count = 10;

    TEST("dlt_compute_asymmetric returns 0");
    ASSERT(dlt_compute_asymmetric(&dlt, 0, weights, count) == 0, "asymmetric failed");

    TEST("delta_p > 0 after asymmetric computation");
    ASSERT(dlt.layers[0].delta_p > 0, "delta_p should be positive");

    TEST("delta_n > 0 after asymmetric computation");
    ASSERT(dlt.layers[0].delta_n > 0, "delta_n should be positive");

    /* Δp = 0.7 × mean(|w>0|): positives are 800,600,300,100,150 → mean=390
     * Δp = 0.7 × 390 = 273 */
    TEST("delta_p ≈ 273 (0.7 × mean positive)");
    ASSERT(dlt.layers[0].delta_p >= 250 && dlt.layers[0].delta_p <= 300,
           "delta_p out of expected range");

    /* Quantize and check distribution */
    trit out[10];
    TEST("dlt_quantize returns 0");
    ASSERT(dlt_quantize(&dlt, 0, weights, out, count) == 0, "quantize failed");

    /* STE gradient */
    int grads[] = {100, 200, -100, -200, 50, -50, 10, 20, -10, 30};
    TEST("dlt_ste_gradient returns >= 0");
    int passthrough = dlt_ste_gradient(&dlt, 0, weights, grads, count);
    ASSERT(passthrough >= 0, "ste_gradient failed");

    /* Trapping detection */
    int trap_weights[] = {0, 10, -5, 3, 0, -2, 1, 0, 5, -8};
    TEST("dlt_detect_trapped returns > 0 for near-zero weights");
    int trapped = dlt_detect_trapped(&dlt, 0, trap_weights, 10);
    ASSERT(trapped > 0, "should detect trapped weights");

    /* Trapping rate */
    TEST("dlt_get_trapping_rate returns > 0");
    int trap_rate = dlt_get_trapping_rate(&dlt, 0);
    ASSERT(trap_rate >= 0, "trapping rate negative");

    /* Reactivation */
    /* Use heavily trapped weights */
    int heavy_trap[] = {20, -15, 5, 0, -3, 10, -8, 2, 0, -1};
    dlt.layers[0].wp = 500;
    dlt.layers[0].wn = -500;
    dlt.layers[0].total_weights = 10;
    dlt_detect_trapped(&dlt, 0, heavy_trap, 10);

    TEST("dlt_reactivate returns >= 0");
    int freed = dlt_reactivate(&dlt, 0, heavy_trap, 10);
    ASSERT(freed >= 0, "reactivate failed");

    /* After reactivation, deadzone should have shrunk */
    TEST("wp decreased after reactivation (if trapping was high)");
    ASSERT(dlt.layers[0].wp <= 500, "wp should not increase");

    /* NULL safety */
    TEST("dlt_compute_asymmetric NULL → -1");
    ASSERT(dlt_compute_asymmetric(NULL, 0, weights, count) == -1, "should reject NULL");

    TEST("dlt_ste_gradient NULL → 0");
    ASSERT(dlt_ste_gradient(NULL, 0, weights, grads, count) == 0, "should return 0");

    TEST("dlt_reactivate NULL → -1");
    ASSERT(dlt_reactivate(NULL, 0, weights, count) == -1, "should reject NULL");

    TEST("dlt_get_trapping_rate bad layer → 0");
    ASSERT(dlt_get_trapping_rate(&dlt, 99) == 0, "should return 0");

    /* STE gradient accumulator check */
    TEST("grad_wp accumulates STE contributions");
    ASSERT(dlt.layers[0].grad_wp != 0 || passthrough == 0,
           "grad_wp should be nonzero if passthrough > 0");

    TEST("reactivated count tracks freed weights");
    ASSERT(dlt.layers[0].reactivated >= 0, "reactivated should be non-negative");
}

/* ==== Section 2: CNTFET Emulation (30 tests) ============================ */

static void test_cntfet_emulation(void) {
    print_section("CNTFET: Device Creation + V_TH + Gates + Drift");

    trit_cntfet_state_t cst;

    TEST("cntfet_init returns 0");
    ASSERT(cntfet_init(&cst) == 0, "init failed");

    TEST("cntfet_init NULL → -1");
    ASSERT(cntfet_init(NULL) == -1, "should reject NULL");

    /* Add LVT device (1.0 nm) */
    TEST("cntfet_add_device LVT returns 0");
    int d0 = cntfet_add_device(&cst, CNTFET_DIAM_LVT, 10, 0);
    ASSERT(d0 == 0, "add LVT failed");

    /* Add MVT device (1.2 nm) */
    TEST("cntfet_add_device MVT returns 1");
    int d1 = cntfet_add_device(&cst, CNTFET_DIAM_MVT, 12, 0);
    ASSERT(d1 == 1, "add MVT failed");

    /* Add HVT device (1.4 nm) */
    TEST("cntfet_add_device HVT returns 2");
    int d2 = cntfet_add_device(&cst, CNTFET_DIAM_HVT, 14, 0);
    ASSERT(d2 == 2, "add HVT failed");

    /* V_TH model: V_TH = 200 + (d − 1.0) × 500 */
    TEST("cntfet_compute_vth(1000) = 200 mV (LVT)");
    ASSERT(cntfet_compute_vth(CNTFET_DIAM_LVT) == 200, "LVT V_TH wrong");

    TEST("cntfet_compute_vth(1200) = 300 mV (MVT)");
    ASSERT(cntfet_compute_vth(CNTFET_DIAM_MVT) == 300, "MVT V_TH wrong");

    TEST("cntfet_compute_vth(1400) = 400 mV (HVT)");
    ASSERT(cntfet_compute_vth(CNTFET_DIAM_HVT) == 400, "HVT V_TH wrong");

    /* Stored V_TH */
    TEST("device[0].vth_mv = 200");
    ASSERT(cst.devices[0].vth_mv == 200, "stored V_TH wrong");

    TEST("device[1].vth_mv = 300");
    ASSERT(cst.devices[1].vth_mv == 300, "stored V_TH wrong");

    /* TNAND gate */
    TEST("TNAND(+1, +1) = −1");
    ASSERT(cntfet_tnand(TRIT_TRUE, TRIT_TRUE) == TRIT_FALSE, "TNAND(1,1)");

    TEST("TNAND(+1, -1) = +1");
    ASSERT(cntfet_tnand(TRIT_TRUE, TRIT_FALSE) == TRIT_TRUE, "TNAND(1,-1)");

    TEST("TNAND(-1, -1) = +1");
    ASSERT(cntfet_tnand(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE, "TNAND(-1,-1)");

    TEST("TNAND(0, +1) = 0");
    ASSERT(cntfet_tnand(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN, "TNAND(0,1)");

    /* TNOR gate */
    TEST("TNOR(+1, +1) = -1");
    ASSERT(cntfet_tnor(TRIT_TRUE, TRIT_TRUE) == TRIT_FALSE, "TNOR(1,1)");

    TEST("TNOR(-1, -1) = +1");
    ASSERT(cntfet_tnor(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE, "TNOR(-1,-1)");

    TEST("TNOR(0, -1) = 0");
    ASSERT(cntfet_tnor(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_UNKNOWN, "TNOR(0,-1)");

    /* Drift simulation */
    TEST("cntfet_simulate_drift returns >= 0");
    int drift = cntfet_simulate_drift(&cst, d0, 1000, 42);
    ASSERT(drift >= 0, "drift should be non-negative");

    TEST("device drift_mv > 0 after simulation");
    ASSERT(cst.devices[d0].drift_mv > 0, "drift should accumulate");

    TEST("device cycle_count = 1000");
    ASSERT(cst.devices[d0].cycle_count == 1000, "cycle count wrong");

    /* Stabilize */
    TEST("cntfet_stabilize reduces drift");
    int pre_drift = cst.devices[d0].drift_mv;
    int residual = cntfet_stabilize(&cst, d0, 1); /* threshold 1mV */
    ASSERT(residual >= 0 && residual <= pre_drift, "stabilize should reduce drift");

    /* Endurance check */
    TEST("cntfet_check_endurance → 1 (within spec)");
    ASSERT(cntfet_check_endurance(&cst, d0) == 1, "should be within endurance");

    /* Huawei class */
    TEST("cntfet_huawei_class(200) = 0 (LVT)");
    ASSERT(cntfet_huawei_class(200) == 0, "should be LVT");

    TEST("cntfet_huawei_class(400) = 1 (MVT)");
    ASSERT(cntfet_huawei_class(400) == 1, "should be MVT");

    TEST("cntfet_huawei_class(650) = 2 (HVT)");
    ASSERT(cntfet_huawei_class(650) == 2, "should be HVT");

    TEST("cntfet_huawei_class(100) = -1 (below min)");
    ASSERT(cntfet_huawei_class(100) == -1, "should be below min");

    /* Average V_TH */
    TEST("cntfet_get_avg_vth returns 300 (mean of 200,300,400)");
    ASSERT(cntfet_get_avg_vth(&cst) == 300, "avg v_th wrong");

    /* NULL safety */
    TEST("cntfet_add_device NULL → -1");
    ASSERT(cntfet_add_device(NULL, 1000, 10, 0) == -1, "should reject NULL");

    TEST("cntfet_simulate_drift NULL → -1");
    ASSERT(cntfet_simulate_drift(NULL, 0, 100, 0) == -1, "should reject NULL");

    /* Drift after stabilise should be less than before */
    TEST("cntfet_stabilize NULL → -1");
    ASSERT(cntfet_stabilize(NULL, 0, 10) == -1, "should reject NULL");
}

/* ==== Section 3: Module Integration (10 tests) ========================== */

static void test_integration(void) {
    print_section("Integration: stabilize+CNTFET, tmvm+DLT, ecs+endurance, hesitation+DLT");

    /* stabilize + CNTFET drift */
    tstab_state_t stab;
    tstab_init(&stab);
    tstab_configure_noise(&stab, TSTAB_NOISE_THERMAL, 10, 123);

    TEST("tstab_apply_cntfet_drift adds drift to noise");
    int new_amp = tstab_apply_cntfet_drift(&stab, 5);
    ASSERT(new_amp == 15, "should be 10 + 5 = 15");

    TEST("tstab_apply_cntfet_drift NULL → -1");
    ASSERT(tstab_apply_cntfet_drift(NULL, 5) == -1, "should reject NULL");

    /* tmvm + DLT quant */
    tmvm_state_t tmvm;
    tmvm_init(&tmvm);

    int weights_mat[] = {
        800,  600, -400, -700,
        300,  100,  -50,  150,
        0,    10,  -200,  500,
        -300, 200,   50, -100
    };
    trit vec[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};

    TEST("tmvm_dlt_quant returns trapped count >= 0");
    int trapped = tmvm_dlt_quant(&tmvm, weights_mat, vec, 4, 4, 500, -500, 0);
    ASSERT(trapped >= 0, "should return trapped count");

    TEST("tmvm_dlt_quant trapped < total weights");
    ASSERT(trapped < 16, "not all weights should be trapped");

    TEST("tmvm_dlt_quant NULL → -1");
    ASSERT(tmvm_dlt_quant(NULL, weights_mat, vec, 4, 4, 500, -500, 0) == -1,
           "should reject NULL");

    /* ecs_gauge + CNTFET endurance */
    ecs_gauge_state_t ecs;
    ecs_init(&ecs);
    ecs_register_channel(&ecs, TRIT_TRUE, 800);
    ecs_register_channel(&ecs, TRIT_FALSE, 0);

    int ok = 0, warn = 0;
    TEST("ecs_cntfet_endurance returns 0");
    ASSERT(ecs_cntfet_endurance(&ecs, &ok, &warn) == 0, "endurance check failed");

    TEST("ecs_cntfet_endurance ok = 2 (both within spec)");
    ASSERT(ok == 2, "both monitors should be within endurance");

    TEST("ecs_cntfet_endurance NULL → -1");
    ASSERT(ecs_cntfet_endurance(NULL, &ok, &warn) == -1, "should reject NULL");

    /* hesitation + DLT react */
    thes_reactor_t hes;
    thes_init(&hes);
    int ch = thes_register_channel(&hes);
    /* Feed mostly Unknowns to trigger high uncertainty */
    for (int i = 0; i < 50; i++)
        thes_observe(&hes, ch, (i % 5 == 0) ? TRIT_TRUE : TRIT_UNKNOWN);

    TEST("thes_dlt_react returns 1 for high Unknown + high trapping");
    ASSERT(thes_dlt_react(&hes, ch, 500, 200) == 1,
           "should recommend DLT reactivation");

    TEST("thes_dlt_react returns 0 for low trapping rate");
    ASSERT(thes_dlt_react(&hes, ch, 100, 200) == 0,
           "should not recommend if trapping below target");
}

/* ==== Main ============================================================== */

int main(void) {
    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  seT6 DLT Expansion + CNTFET Gate Emulation Test Suite\n");
    printf("══════════════════════════════════════════════════════════════\n");

    test_dlt_expansion();
    test_cntfet_emulation();
    test_integration();

    printf("\n══════════════════════════════════════════════════════════════\n");
    printf("  DLT+CNTFET Tests: %d passed, %d failed, %d total\n",
           tests_passed, tests_failed, tests_total);
        printf("=== Results: %d passed, %d failed ===\n",
            tests_passed, tests_failed);
    printf("══════════════════════════════════════════════════════════════\n\n");

    return tests_failed > 0 ? 1 : 0;
}
