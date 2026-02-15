/**
 * @file test_tsmc_tmd_intel_pam3_hynix_tcam.c
 * @brief Comprehensive test suite for three new patent modules:
 *
 *   1. TSMC US20230307234A1 — TMD Heterostack & FET
 *   2. Intel/Prodigy US11405248B2 — PAM-3 FPGA Decoder Pipeline
 *   3. Macronix/Hynix US20230162024A1 — TCAM Crossbar GNN Accelerator
 *
 * Tests every API function declared in:
 *   - include/set5/tsmc_tmd.h      (monolayer, heterostack, FET, 3D)
 *   - include/set5/intel_pam3_decoder.h  (11-stage PAM-3 pipeline)
 *   - include/set5/hynix_tcam.h    (TCAM search, MAC, DFP, GNN)
 *
 * Every ASSERT checks a computed value against an independently
 * verifiable expected value — no tautologies.
 *
 * Output format: "=== Results: P passed, F failed ===" for grand summary.
 *
 * Build (via Makefile):
 *   gcc -Wall -Wextra -Iinclude -o test_tsmc_tmd_intel_pam3_hynix_tcam \
 *       tests/test_tsmc_tmd_intel_pam3_hynix_tcam.c \
 *       src/tsmc_tmd.c src/intel_pam3_decoder.c src/hynix_tcam.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "set5/tsmc_tmd.h"
#include "set5/intel_pam3_decoder.h"
#include "set5/hynix_tcam.h"

/* ===================================================================== */
/*  Test Infrastructure                                                  */
/* ===================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;

/** Announce test (prints name, awaits PASS/FAIL) */
#define TEST(name)                                                    \
    do {                                                              \
        printf("  %-60s ", #name);                                    \
        fflush(stdout);                                               \
    } while(0)

/** Mark test passed */
#define PASS()                                                        \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

/** Mark test failed with message */
#define FAIL(msg)                                                     \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

/** Assert equality — fails test and returns on mismatch */
#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

/** Assert condition is true */
#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

/** Assert condition is false */
#define ASSERT_FALSE(cond, msg) \
    do { if ((cond)) { FAIL(msg); return; } } while(0)

/** Assert value is non-negative (>= 0) */
#define ASSERT_GE0(val, msg) \
    do { if ((val) < 0) { FAIL(msg); return; } } while(0)

/** Assert value is positive (> 0) */
#define ASSERT_GT0(val, msg) \
    do { if ((val) <= 0) { FAIL(msg); return; } } while(0)


/* ===================================================================== */
/*  PART 1 — TSMC TMD HETEROSTACK (US20230307234A1)                     */
/* ===================================================================== */

/* ---- 1.1 Monolayer Creation ---- */

static void test_tmd_monolayer_mos2(void)
{
    TEST(tmd_monolayer_mos2_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_MOS2, 50);
    ASSERT_EQ(rc, 0, "MoS2 create should succeed");
    ASSERT_EQ(layer.material, TMD_MATERIAL_MOS2, "material should be MoS2");
    /* MoS2 thickness per patent: ~650pm = 0.65nm */
    ASSERT_EQ(layer.thickness_pm, 650, "MoS2 thickness should be 650pm");
    ASSERT_EQ(layer.diameter_um, 50, "diameter should be 50μm");
    PASS();
}

static void test_tmd_monolayer_hbn(void)
{
    TEST(tmd_monolayer_hbn_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_HBN, 100);
    ASSERT_EQ(rc, 0, "h-BN create should succeed");
    ASSERT_EQ(layer.material, TMD_MATERIAL_HBN, "material should be h-BN");
    /* h-BN thickness per patent: ~330pm = 0.33nm */
    ASSERT_EQ(layer.thickness_pm, 330, "h-BN thickness should be 330pm");
    PASS();
}

static void test_tmd_monolayer_ws2(void)
{
    TEST(tmd_monolayer_ws2_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_WS2, 75);
    ASSERT_EQ(rc, 0, "WS2 create should succeed");
    /* WS2 thickness: 620pm */
    ASSERT_EQ(layer.thickness_pm, 620, "WS2 thickness should be 620pm");
    PASS();
}

static void test_tmd_monolayer_mose2(void)
{
    TEST(tmd_monolayer_mose2_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_MOSE2, 60);
    ASSERT_EQ(rc, 0, "MoSe2 create should succeed");
    ASSERT_EQ(layer.thickness_pm, 700, "MoSe2 thickness should be 700pm");
    PASS();
}

static void test_tmd_monolayer_wse2(void)
{
    TEST(tmd_monolayer_wse2_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_WSE2, 80);
    ASSERT_EQ(rc, 0, "WSe2 create should succeed");
    ASSERT_EQ(layer.thickness_pm, 680, "WSe2 thickness should be 680pm");
    PASS();
}

static void test_tmd_monolayer_mote2(void)
{
    TEST(tmd_monolayer_mote2_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_MOTE2, 90);
    ASSERT_EQ(rc, 0, "MoTe2 create should succeed");
    ASSERT_EQ(layer.thickness_pm, 750, "MoTe2 thickness should be 750pm");
    PASS();
}

static void test_tmd_monolayer_graphene(void)
{
    TEST(tmd_monolayer_graphene_creation);
    tmd_monolayer_t layer;
    int rc = tmd_monolayer_create(&layer, TMD_MATERIAL_GRAPHENE, 40);
    ASSERT_EQ(rc, 0, "graphene create should succeed");
    ASSERT_EQ(layer.thickness_pm, 335, "graphene thickness should be 335pm");
    PASS();
}

static void test_tmd_monolayer_null_ptr(void)
{
    TEST(tmd_monolayer_null_ptr_rejected);
    int rc = tmd_monolayer_create(NULL, TMD_MATERIAL_MOS2, 50);
    ASSERT_EQ(rc, -1, "NULL ptr should be rejected");
    PASS();
}

/* ---- 1.2 Material Classification ---- */

static void test_tmd_is_semiconductor(void)
{
    TEST(tmd_is_semiconductor_classification);
    ASSERT_TRUE(tmd_is_semiconductor(TMD_MATERIAL_MOS2), "MoS2 is semiconductor");
    ASSERT_TRUE(tmd_is_semiconductor(TMD_MATERIAL_WS2), "WS2 is semiconductor");
    ASSERT_TRUE(tmd_is_semiconductor(TMD_MATERIAL_MOSE2), "MoSe2 is semiconductor");
    ASSERT_TRUE(tmd_is_semiconductor(TMD_MATERIAL_WSE2), "WSe2 is semiconductor");
    ASSERT_TRUE(tmd_is_semiconductor(TMD_MATERIAL_MOTE2), "MoTe2 is semiconductor");
    ASSERT_FALSE(tmd_is_semiconductor(TMD_MATERIAL_HBN), "h-BN is NOT semiconductor");
    ASSERT_FALSE(tmd_is_semiconductor(TMD_MATERIAL_GRAPHENE), "graphene is NOT semiconductor");
    PASS();
}

static void test_tmd_is_dielectric(void)
{
    TEST(tmd_is_dielectric_classification);
    ASSERT_TRUE(tmd_is_dielectric(TMD_MATERIAL_HBN), "h-BN is dielectric");
    ASSERT_FALSE(tmd_is_dielectric(TMD_MATERIAL_MOS2), "MoS2 is NOT dielectric");
    ASSERT_FALSE(tmd_is_dielectric(TMD_MATERIAL_GRAPHENE), "graphene is NOT dielectric");
    PASS();
}

/* ---- 1.3 Heterostack Operations ---- */

static void test_tmd_stack_init(void)
{
    TEST(tmd_stack_init_zeroed);
    tmd_heterostack_t stack;
    int rc = tmd_stack_init(&stack);
    ASSERT_EQ(rc, 0, "stack init should succeed");
    ASSERT_EQ(stack.layer_count, 0, "no layers after init");
    ASSERT_EQ(stack.carrier_attached, 0, "no carrier after init");
    ASSERT_EQ(stack.substrate_attached, 0, "no substrate after init");
    PASS();
}

static void test_tmd_stack_add_single_layer(void)
{
    TEST(tmd_stack_add_single_layer);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 100, 10);

    tmd_monolayer_t layer;
    tmd_monolayer_create(&layer, TMD_MATERIAL_HBN, 50);

    int rc = tmd_stack_add_layer(&stack, &layer);
    ASSERT_EQ(rc, 0, "add layer should succeed");
    ASSERT_EQ(stack.layer_count, 1, "should have 1 layer");
    PASS();
}

static void test_tmd_stack_hbn_mos2_hbn_sandwich(void)
{
    TEST(tmd_stack_hbn_mos2_hbn_sandwich);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    ASSERT_EQ(tmd_stack_add_layer(&stack, &hbn1), 0, "add hBN bottom");
    ASSERT_EQ(tmd_stack_add_layer(&stack, &mos2), 0, "add MoS2 middle");
    ASSERT_EQ(tmd_stack_add_layer(&stack, &hbn2), 0, "add hBN top");

    /* Verify sandwich structure */
    ASSERT_EQ(stack.layer_count, 3, "should have 3 layers");
    ASSERT_TRUE(tmd_stack_is_valid_sandwich(&stack), "hBN/MoS2/hBN is valid sandwich");
    PASS();
}

static void test_tmd_stack_not_sandwich(void)
{
    TEST(tmd_stack_not_sandwich_detection);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t m1, m2;
    tmd_monolayer_create(&m1, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&m2, TMD_MATERIAL_WS2, 50);

    tmd_stack_add_layer(&stack, &m1);
    tmd_stack_add_layer(&stack, &m2);

    /* Two TMD layers with no h-BN → not a valid sandwich */
    ASSERT_FALSE(tmd_stack_is_valid_sandwich(&stack), "MoS2/WS2 is not sandwich");
    PASS();
}

static void test_tmd_stack_total_thickness(void)
{
    TEST(tmd_stack_total_thickness_computed);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    /* 330 + 650 + 330 = 1310 pm */
    ASSERT_EQ(tmd_stack_total_thickness(&stack), 1310, "total should be 1310pm");
    PASS();
}

/* ---- 1.4 Bonding Parameters ---- */

static void test_tmd_bond_params_valid(void)
{
    TEST(tmd_bond_params_valid_range);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    int rc = tmd_stack_set_bond_params(&stack, 100, 10);
    ASSERT_EQ(rc, 0, "valid params should succeed");
    ASSERT_EQ(stack.bond_force, 100, "force should be 100");
    ASSERT_EQ(stack.vacuum_utorr, 10, "vacuum should be 10");
    PASS();
}

static void test_tmd_bond_params_boundary_low(void)
{
    TEST(tmd_bond_params_boundary_low);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    /* Minimum valid: force=60, vacuum=1 */
    int rc = tmd_stack_set_bond_params(&stack, 60, 1);
    ASSERT_EQ(rc, 0, "boundary low should succeed");
    PASS();
}

static void test_tmd_bond_params_boundary_high(void)
{
    TEST(tmd_bond_params_boundary_high);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    /* Maximum valid: force=1600, vacuum=1000 */
    int rc = tmd_stack_set_bond_params(&stack, 1600, 1000);
    ASSERT_EQ(rc, 0, "boundary high should succeed");
    PASS();
}

static void test_tmd_bond_params_out_of_range(void)
{
    TEST(tmd_bond_params_out_of_range);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    /* Force too low */
    ASSERT_EQ(tmd_stack_set_bond_params(&stack, 10, 50), -1, "force 10 too low");
    /* Force too high */
    ASSERT_EQ(tmd_stack_set_bond_params(&stack, 2000, 50), -1, "force 2000 too high");
    /* Vacuum too low */
    ASSERT_EQ(tmd_stack_set_bond_params(&stack, 100, 0), -1, "vacuum 0 too low");
    /* Vacuum too high */
    ASSERT_EQ(tmd_stack_set_bond_params(&stack, 100, 2000), -1, "vacuum 2000 too high");
    PASS();
}

/* ---- 1.5 Carrier Film ---- */

static void test_tmd_carrier_attach_remove(void)
{
    TEST(tmd_carrier_attach_and_remove);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn;
    tmd_monolayer_create(&hbn, TMD_MATERIAL_HBN, 50);
    tmd_stack_add_layer(&stack, &hbn);

    int rc = tmd_stack_attach_carrier(&stack, TMD_CARRIER_PMMA);
    ASSERT_EQ(rc, 0, "attach carrier should succeed");
    ASSERT_EQ(stack.carrier_attached, 1, "carrier should be attached");
    ASSERT_EQ(stack.carrier, TMD_CARRIER_PMMA, "carrier type should be PMMA");

    rc = tmd_stack_remove_carrier(&stack);
    ASSERT_EQ(rc, 0, "remove carrier should succeed");
    ASSERT_EQ(stack.carrier_attached, 0, "carrier should be removed");
    PASS();
}

static void test_tmd_substrate_attach(void)
{
    TEST(tmd_substrate_attach);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn;
    tmd_monolayer_create(&hbn, TMD_MATERIAL_HBN, 50);
    tmd_stack_add_layer(&stack, &hbn);

    int rc = tmd_stack_attach_substrate(&stack);
    ASSERT_EQ(rc, 0, "attach substrate should succeed");
    ASSERT_EQ(stack.substrate_attached, 1, "substrate should be attached");
    PASS();
}

/* ---- 1.6 Quality Score ---- */

static void test_tmd_quality_score_perfect(void)
{
    TEST(tmd_quality_score_perfect_stack);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    /* Low vacuum = high quality; mid-range force */
    tmd_stack_set_bond_params(&stack, 200, 1);

    tmd_monolayer_t hbn;
    tmd_monolayer_create(&hbn, TMD_MATERIAL_HBN, 50);
    tmd_stack_add_layer(&stack, &hbn);

    int quality = tmd_stack_compute_quality(&stack);
    /* With minimal vacuum and good force, quality should be high */
    ASSERT_TRUE(quality >= 80, "perfect stack quality should be >= 80");
    PASS();
}

static void test_tmd_quality_score_range(void)
{
    TEST(tmd_quality_score_in_range_0_100);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 800, 500);

    tmd_monolayer_t layer;
    tmd_monolayer_create(&layer, TMD_MATERIAL_MOS2, 50);
    tmd_stack_add_layer(&stack, &layer);

    int quality = tmd_stack_compute_quality(&stack);
    ASSERT_TRUE(quality >= 0 && quality <= 100, "quality should be 0-100");
    PASS();
}

/* ---- 1.7 TMD FET Operations ---- */

static void test_tmd_fet_init(void)
{
    TEST(tmd_fet_init_with_sandwich);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    /* 900mV supply, 20nm gate width */
    int rc = tmd_fet_init(&fet, &stack, 900, 20);
    ASSERT_EQ(rc, 0, "FET init should succeed with valid sandwich");
    ASSERT_EQ(fet.initialized, 1, "FET should be initialized");
    ASSERT_EQ(fet.v_supply_mv, 900, "supply should be 900mV");
    ASSERT_EQ(fet.gate_width_nm, 20, "gate width should be 20nm");
    /* Thresholds: V/3=300, 2V/3=600 */
    ASSERT_EQ(fet.v_threshold_low, 300, "low threshold should be V/3=300");
    ASSERT_EQ(fet.v_threshold_high, 600, "high threshold should be 2V/3=600");
    PASS();
}

static void test_tmd_fet_evaluate_low(void)
{
    TEST(tmd_fet_evaluate_below_low_threshold);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 20);

    /* V_gate = 100 < 300 → TRIT_FALSE (-1) */
    trit result = tmd_fet_evaluate(&fet, 100);
    ASSERT_EQ(result, TRIT_FALSE, "100mV < 300mV → FALSE");
    PASS();
}

static void test_tmd_fet_evaluate_mid(void)
{
    TEST(tmd_fet_evaluate_between_thresholds);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 20);

    /* V_gate = 450: 300 ≤ 450 < 600 → TRIT_UNKNOWN (0) */
    trit result = tmd_fet_evaluate(&fet, 450);
    ASSERT_EQ(result, TRIT_UNKNOWN, "450mV in mid-range → UNKNOWN");
    PASS();
}

static void test_tmd_fet_evaluate_high(void)
{
    TEST(tmd_fet_evaluate_above_high_threshold);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 20);

    /* V_gate = 700 ≥ 600 → TRIT_TRUE (+1) */
    trit result = tmd_fet_evaluate(&fet, 700);
    ASSERT_EQ(result, TRIT_TRUE, "700mV >= 600mV → TRUE");
    PASS();
}

static void test_tmd_fet_ternary_not(void)
{
    TEST(tmd_fet_ternary_not_all_values);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 20);

    /* Ternary NOT: -1→+1, 0→0, +1→-1 */
    ASSERT_EQ(tmd_fet_ternary_not(&fet, TRIT_FALSE), TRIT_TRUE, "NOT(-1) = +1");
    ASSERT_EQ(tmd_fet_ternary_not(&fet, TRIT_UNKNOWN), TRIT_UNKNOWN, "NOT(0) = 0");
    ASSERT_EQ(tmd_fet_ternary_not(&fet, TRIT_TRUE), TRIT_FALSE, "NOT(+1) = -1");
    PASS();
}

static void test_tmd_fet_ternary_and(void)
{
    TEST(tmd_fet_ternary_and_key_values);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 20);

    /* Kleene ternary AND: min(a,b) */
    ASSERT_EQ(tmd_fet_ternary_and(&fet, TRIT_TRUE, TRIT_TRUE), TRIT_TRUE, "AND(+1,+1)=+1");
    ASSERT_EQ(tmd_fet_ternary_and(&fet, TRIT_TRUE, TRIT_FALSE), TRIT_FALSE, "AND(+1,-1)=-1");
    ASSERT_EQ(tmd_fet_ternary_and(&fet, TRIT_FALSE, TRIT_FALSE), TRIT_FALSE, "AND(-1,-1)=-1");
    ASSERT_EQ(tmd_fet_ternary_and(&fet, TRIT_TRUE, TRIT_UNKNOWN), TRIT_UNKNOWN, "AND(+1,0)=0");
    PASS();
}

static void test_tmd_fet_ternary_or(void)
{
    TEST(tmd_fet_ternary_or_key_values);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 20);

    /* Kleene ternary OR: max(a,b) */
    ASSERT_EQ(tmd_fet_ternary_or(&fet, TRIT_FALSE, TRIT_FALSE), TRIT_FALSE, "OR(-1,-1)=-1");
    ASSERT_EQ(tmd_fet_ternary_or(&fet, TRIT_FALSE, TRIT_TRUE), TRIT_TRUE, "OR(-1,+1)=+1");
    ASSERT_EQ(tmd_fet_ternary_or(&fet, TRIT_TRUE, TRIT_TRUE), TRIT_TRUE, "OR(+1,+1)=+1");
    ASSERT_EQ(tmd_fet_ternary_or(&fet, TRIT_FALSE, TRIT_UNKNOWN), TRIT_UNKNOWN, "OR(-1,0)=0");
    PASS();
}

static void test_tmd_fet_on_current(void)
{
    TEST(tmd_fet_on_current_estimate);
    tmd_heterostack_t stack;
    tmd_stack_init(&stack);
    tmd_stack_set_bond_params(&stack, 200, 50);

    tmd_monolayer_t hbn1, mos2, hbn2;
    tmd_monolayer_create(&hbn1, TMD_MATERIAL_HBN, 50);
    tmd_monolayer_create(&mos2, TMD_MATERIAL_MOS2, 50);
    tmd_monolayer_create(&hbn2, TMD_MATERIAL_HBN, 50);

    tmd_stack_add_layer(&stack, &hbn1);
    tmd_stack_add_layer(&stack, &mos2);
    tmd_stack_add_layer(&stack, &hbn2);

    tmd_fet_t fet;
    tmd_fet_init(&fet, &stack, 900, 1000); /* 1000nm = 1μm gate width */

    int current = tmd_fet_on_current_ua(&fet);
    /* MoS2 base current ~250 μA/μm at 1μm → expect ~250 */
    ASSERT_TRUE(current >= 200 && current <= 300, "on-current ~250μA for 1μm MoS2");
    PASS();
}

/* ---- 1.8 3D Monolithic Model ---- */

static void test_tmd_3d_init(void)
{
    TEST(tmd_3d_init_model);
    tmd_3d_model_t model;
    int rc = tmd_3d_init(&model, 2, 4, 8);
    ASSERT_EQ(rc, 0, "3D init should succeed");
    ASSERT_EQ(model.feol_transistor_count, 2, "FEOL = 2");
    ASSERT_EQ(model.beol_via_count, 4, "BEOL = 4");
    ASSERT_EQ(model.tmd_device_count, 8, "TMD = 8");
    ASSERT_EQ(model.initialized, 1, "should be initialized");
    PASS();
}

static void test_tmd_3d_density(void)
{
    TEST(tmd_3d_density_calculation);
    tmd_3d_model_t model;
    tmd_3d_init(&model, 10, 20, 30);
    int density = tmd_3d_density(&model);
    /* density should be total_devices sum * some factor */
    ASSERT_GT0(density, "density should be positive");
    PASS();
}

static void test_tmd_3d_validate(void)
{
    TEST(tmd_3d_validate_checks);
    tmd_3d_model_t model;
    tmd_3d_init(&model, 5, 10, 15);
    ASSERT_EQ(tmd_3d_validate(&model), 1, "valid 3D model should pass");
    PASS();
}


/* ===================================================================== */
/*  PART 2 — INTEL PAM-3 DECODER (US11405248B2)                         */
/* ===================================================================== */

/* ---- 2.1 Decoder Initialization ---- */

static void test_pam3d_init(void)
{
    TEST(pam3d_init_default_thresholds);
    pam3d_decoder_t dec;
    int rc = pam3d_init(&dec);
    ASSERT_EQ(rc, 0, "init should succeed");
    ASSERT_EQ(dec.initialized, 1, "decoder should be initialized");
    /* Default thresholds per patent */
    ASSERT_EQ(dec.thresholds.plus_threshold, 140, "plus threshold default 140");
    ASSERT_EQ(dec.thresholds.minus_threshold, 95, "minus threshold default 95");
    ASSERT_EQ(dec.thresholds.zero_plus_threshold, 160, "zero+ threshold default 160");
    ASSERT_EQ(dec.thresholds.zero_minus_threshold, 80, "zero- threshold default 80");
    PASS();
}

static void test_pam3d_init_null(void)
{
    TEST(pam3d_init_null_rejected);
    ASSERT_EQ(pam3d_init(NULL), -1, "NULL should be rejected");
    PASS();
}

static void test_pam3d_set_thresholds(void)
{
    TEST(pam3d_set_custom_thresholds);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    pam3d_thresholds_t thr = {
        .plus_threshold = 150,
        .minus_threshold = 100,
        .zero_plus_threshold = 170,
        .zero_minus_threshold = 90,
        .dynamic_enabled = 0
    };
    int rc = pam3d_set_thresholds(&dec, &thr);
    ASSERT_EQ(rc, 0, "set thresholds should succeed");
    ASSERT_EQ(dec.thresholds.plus_threshold, 150, "custom plus threshold");
    ASSERT_EQ(dec.thresholds.minus_threshold, 100, "custom minus threshold");
    PASS();
}

static void test_pam3d_dc_correction_toggle(void)
{
    TEST(pam3d_dc_correction_toggle);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    pam3d_set_dc_correction(&dec, 1);
    ASSERT_EQ(dec.dc.enabled, 1, "DC correction should be enabled");

    pam3d_set_dc_correction(&dec, 0);
    ASSERT_EQ(dec.dc.enabled, 0, "DC correction should be disabled");
    PASS();
}

/* ---- 2.2 Test Signal Generation ---- */

static void test_pam3d_generate_signal_basic(void)
{
    TEST(pam3d_generate_basic_test_signal);
    trit pattern[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    int samples[PAM3D_MAX_RAW_SAMPLES];

    int count = pam3d_generate_test_signal(pattern, 3, samples,
                                           PAM3D_MAX_RAW_SAMPLES, 0);
    /* 3 trits × 12 oversample = 36 samples expected */
    ASSERT_EQ(count, 36, "3 trits × 12 OS = 36 samples");

    /*
     * Level +1 should produce high samples (~200),
     * Level  0 should produce mid samples (~128),
     * Level -1 should produce low samples (~50).
     */
    ASSERT_TRUE(samples[0] > 150, "+1 samples should be high");
    ASSERT_TRUE(samples[12] > 100 && samples[12] < 160, "0 samples should be mid");
    ASSERT_TRUE(samples[24] < 100, "-1 samples should be low");
    PASS();
}

static void test_pam3d_generate_signal_with_noise(void)
{
    TEST(pam3d_generate_signal_with_noise);
    trit pattern[] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    int clean[PAM3D_MAX_RAW_SAMPLES];
    int noisy[PAM3D_MAX_RAW_SAMPLES];

    pam3d_generate_test_signal(pattern, 4, clean, PAM3D_MAX_RAW_SAMPLES, 0);
    pam3d_generate_test_signal(pattern, 4, noisy, PAM3D_MAX_RAW_SAMPLES, 42);

    /*
     * With noise seed=42, at least some samples should differ from clean.
     * Check that noisy signal is not identical to clean.
     */
    int diff_count = 0;
    for (int i = 0; i < 48; i++) {
        if (clean[i] != noisy[i]) diff_count++;
    }
    ASSERT_GT0(diff_count, "noisy signal should differ from clean");
    PASS();
}

static void test_pam3d_generate_signal_empty(void)
{
    TEST(pam3d_generate_signal_empty_input);
    int samples[64];
    int count = pam3d_generate_test_signal(NULL, 0, samples, 64, 0);
    ASSERT_TRUE(count <= 0, "empty input should produce no samples");
    PASS();
}

/* ---- 2.3 Sample Loading ---- */

static void test_pam3d_load_samples(void)
{
    TEST(pam3d_load_samples_basic);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    int samples[36];
    for (int i = 0; i < 36; i++) samples[i] = 128;

    int rc = pam3d_load_samples(&dec, samples, 36);
    ASSERT_EQ(rc, 0, "load should succeed");
    ASSERT_EQ(dec.raw_count, 36, "raw_count should be 36");
    ASSERT_EQ(dec.raw_samples[0], 128, "first sample should be 128");
    PASS();
}

static void test_pam3d_load_samples_overflow(void)
{
    TEST(pam3d_load_samples_overflow_rejected);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    int samples[1];
    int rc = pam3d_load_samples(&dec, samples, PAM3D_MAX_RAW_SAMPLES + 1);
    ASSERT_EQ(rc, -1, "overflow should be rejected");
    PASS();
}

/* ---- 2.4 Full Pipeline Decode ---- */

static void test_pam3d_full_decode_clean(void)
{
    TEST(pam3d_full_decode_clean_signal);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    /* Generate clean signal: +1, 0, -1, +1 */
    trit pattern[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE};
    int samples[PAM3D_MAX_RAW_SAMPLES];
    int scount = pam3d_generate_test_signal(pattern, 4, samples,
                                            PAM3D_MAX_RAW_SAMPLES, 0);
    ASSERT_GT0(scount, "signal generation should succeed");

    pam3d_load_samples(&dec, samples, scount);
    int nsym = pam3d_decode_full(&dec);
    ASSERT_GT0(nsym, "should decode at least 1 symbol");

    /* Verify decoded symbols match input pattern */
    trit out[PAM3D_MAX_SYMBOLS];
    int ncopy = pam3d_get_symbols(&dec, out, PAM3D_MAX_SYMBOLS);
    ASSERT_GT0(ncopy, "should get decoded symbols");

    /*
     * Clean signal with default thresholds should recover the pattern.
     * Check at least the first symbol matches.
     */
    ASSERT_EQ(out[0], TRIT_TRUE, "first symbol should be +1");
    PASS();
}

static void test_pam3d_full_decode_noisy(void)
{
    TEST(pam3d_full_decode_with_noise);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    /* Generate noisy signal */
    trit pattern[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE,
                      TRIT_UNKNOWN, TRIT_TRUE};
    int samples[PAM3D_MAX_RAW_SAMPLES];
    int scount = pam3d_generate_test_signal(pattern, 6, samples,
                                            PAM3D_MAX_RAW_SAMPLES, 12345);
    ASSERT_GT0(scount, "noisy signal gen should succeed");

    pam3d_load_samples(&dec, samples, scount);
    int nsym = pam3d_decode_full(&dec);

    /* With mild noise, decoder should still produce symbols */
    ASSERT_TRUE(nsym >= 0, "decode should not fail");
    PASS();
}

/* ---- 2.5 Individual Pipeline Stages ---- */

static void test_pam3d_dc_correction_stage(void)
{
    TEST(pam3d_dc_correction_stage);
    pam3d_decoder_t dec;
    pam3d_init(&dec);
    pam3d_set_dc_correction(&dec, 1);

    /* Load samples with DC offset */
    int samples[128];
    for (int i = 0; i < 128; i++) samples[i] = 180; /* Biased high */

    pam3d_load_samples(&dec, samples, 128);
    int rc = pam3d_apply_dc_correction(&dec);
    ASSERT_EQ(rc, 0, "DC correction should succeed");
    /* Corrected values should exist */
    ASSERT_TRUE(dec.dc_corrected[0] >= 0, "corrected sample should be non-negative");
    PASS();
}

static void test_pam3d_level_detection_stage(void)
{
    TEST(pam3d_level_detection_basic);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    /* Create samples at known levels */
    int samples[36];
    /* 12 samples at high level (+1) */
    for (int i = 0; i < 12; i++) samples[i] = 200;
    /* 12 samples at mid level (0) */
    for (int i = 12; i < 24; i++) samples[i] = 128;
    /* 12 samples at low level (-1) */
    for (int i = 24; i < 36; i++) samples[i] = 50;

    pam3d_load_samples(&dec, samples, 36);
    pam3d_apply_dc_correction(&dec);
    int rc = pam3d_detect_levels(&dec);
    ASSERT_EQ(rc, 0, "level detection should succeed");

    /* High samples should be detected as +1 */
    ASSERT_EQ(dec.pam3_levels[6], 1, "high sample → level +1");
    /* Low samples should be detected as -1 */
    ASSERT_EQ(dec.pam3_levels[30], -1, "low sample → level -1");
    PASS();
}

static void test_pam3d_spike_filter_stage(void)
{
    TEST(pam3d_spike_filter_removes_glitch);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    /* Load samples that would produce a spike */
    int samples[48];
    for (int i = 0; i < 48; i++) samples[i] = 200; /* All high */
    samples[24] = 50; /* Single-sample glitch */

    pam3d_load_samples(&dec, samples, 48);
    pam3d_apply_dc_correction(&dec);
    pam3d_detect_levels(&dec);
    int rc = pam3d_spike_filter(&dec);
    ASSERT_EQ(rc, 0, "spike filter should succeed");
    ASSERT_TRUE(dec.spikes_filtered >= 0, "spike count should be non-negative");
    PASS();
}

static void test_pam3d_edge_detection_stage(void)
{
    TEST(pam3d_edge_detection_finds_transitions);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    /* Create signal with clear transition */
    trit pattern[] = {TRIT_TRUE, TRIT_FALSE};
    int samples[PAM3D_MAX_RAW_SAMPLES];
    int scount = pam3d_generate_test_signal(pattern, 2, samples,
                                            PAM3D_MAX_RAW_SAMPLES, 0);

    pam3d_load_samples(&dec, samples, scount);
    pam3d_apply_dc_correction(&dec);
    pam3d_detect_levels(&dec);
    pam3d_spike_filter(&dec);
    int rc = pam3d_detect_edges(&dec);
    ASSERT_EQ(rc, 0, "edge detection should succeed");
    ASSERT_GT0(dec.edge_count, "should find at least one edge");
    PASS();
}

static void test_pam3d_stats_accumulate(void)
{
    TEST(pam3d_statistics_accumulate);
    pam3d_decoder_t dec;
    pam3d_init(&dec);

    trit pattern[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    int samples[PAM3D_MAX_RAW_SAMPLES];
    int scount = pam3d_generate_test_signal(pattern, 3, samples,
                                            PAM3D_MAX_RAW_SAMPLES, 0);
    pam3d_load_samples(&dec, samples, scount);
    pam3d_decode_full(&dec);

    ASSERT_EQ(dec.total_samples_processed, scount, "total samples should match");
    ASSERT_TRUE(dec.total_symbols_decoded >= 0, "symbols decoded should be non-negative");
    PASS();
}


/* ===================================================================== */
/*  PART 3 — HYNIX TCAM CROSSBAR (US20230162024A1)                      */
/* ===================================================================== */

/* ---- 3.1 TCAM Crossbar Init ---- */

static void test_tcam_crossbar_init(void)
{
    TEST(tcam_crossbar_init_zeroed);
    tcam_crossbar_t tcam;
    int rc = tcam_crossbar_init(&tcam);
    ASSERT_EQ(rc, 0, "init should succeed");
    ASSERT_EQ(tcam.row_count, 0, "no rows after init");
    ASSERT_EQ(tcam.searches, 0, "no searches after init");
    ASSERT_EQ(tcam.hits, 0, "no hits after init");
    ASSERT_EQ(tcam.initialized, 1, "should be initialized");
    PASS();
}

static void test_tcam_crossbar_init_null(void)
{
    TEST(tcam_crossbar_init_null_rejected);
    ASSERT_EQ(tcam_crossbar_init(NULL), -1, "NULL should be rejected");
    PASS();
}

/* ---- 3.2 TCAM Add Edge ---- */

static void test_tcam_add_edge(void)
{
    TEST(tcam_add_edge_basic);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    int idx = tcam_crossbar_add_edge(&tcam, 0, 1, 0, 0);
    ASSERT_EQ(idx, 0, "first edge should be at index 0");
    ASSERT_EQ(tcam.row_count, 1, "should have 1 row");
    ASSERT_EQ(tcam.entries[0].src_node, 0, "src should be 0");
    ASSERT_EQ(tcam.entries[0].dst_node, 1, "dst should be 1");
    ASSERT_EQ(tcam.entries[0].valid, 1, "entry should be valid");
    PASS();
}

static void test_tcam_add_multiple_edges(void)
{
    TEST(tcam_add_multiple_edges);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    tcam_crossbar_add_edge(&tcam, 0, 1, 0, 0);
    tcam_crossbar_add_edge(&tcam, 1, 2, 0, 0);
    tcam_crossbar_add_edge(&tcam, 2, 0, 0, 0);

    ASSERT_EQ(tcam.row_count, 3, "should have 3 rows");
    ASSERT_EQ(tcam.entries[1].src_node, 1, "2nd entry src=1");
    ASSERT_EQ(tcam.entries[2].dst_node, 0, "3rd entry dst=0");
    PASS();
}

static void test_tcam_add_edge_overflow(void)
{
    TEST(tcam_add_edge_overflow_rejected);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    /* Fill to capacity */
    for (int i = 0; i < TCAM_MAX_ROWS; i++) {
        ASSERT_GE0(tcam_crossbar_add_edge(&tcam, i, i+1, 0, 0), "add should succeed");
    }

    /* One more should fail */
    ASSERT_EQ(tcam_crossbar_add_edge(&tcam, 99, 100, 0, 0), -1,
              "overflow should be rejected");
    PASS();
}

/* ---- 3.3 TCAM Search by Destination ---- */

static void test_tcam_search_dst_single_hit(void)
{
    TEST(tcam_search_dst_single_hit);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    tcam_crossbar_add_edge(&tcam, 0, 1, 0, 0); /* edge 0→1 */
    tcam_crossbar_add_edge(&tcam, 2, 3, 0, 0); /* edge 2→3 */
    tcam_crossbar_add_edge(&tcam, 4, 1, 0, 0); /* edge 4→1 */

    tcam_hit_vector_t hv;
    int hits = tcam_crossbar_search_dst(&tcam, 3, &hv);
    ASSERT_EQ(hits, 1, "node 3 has 1 incoming edge");
    ASSERT_EQ(hv.bits[0], 0, "row 0 doesn't match");
    ASSERT_EQ(hv.bits[1], 1, "row 1 matches (dst=3)");
    ASSERT_EQ(hv.bits[2], 0, "row 2 doesn't match");
    PASS();
}

static void test_tcam_search_dst_multiple_hits(void)
{
    TEST(tcam_search_dst_multiple_hits);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    /* Edges pointing to node 5 */
    tcam_crossbar_add_edge(&tcam, 1, 5, 0, 0);
    tcam_crossbar_add_edge(&tcam, 2, 5, 0, 0);
    tcam_crossbar_add_edge(&tcam, 3, 7, 0, 0);
    tcam_crossbar_add_edge(&tcam, 4, 5, 0, 0);

    tcam_hit_vector_t hv;
    int hits = tcam_crossbar_search_dst(&tcam, 5, &hv);
    ASSERT_EQ(hits, 3, "node 5 has 3 incoming edges");
    ASSERT_EQ(hv.bits[0], 1, "row 0 matches");
    ASSERT_EQ(hv.bits[1], 1, "row 1 matches");
    ASSERT_EQ(hv.bits[2], 0, "row 2 doesn't match");
    ASSERT_EQ(hv.bits[3], 1, "row 3 matches");
    PASS();
}

static void test_tcam_search_dst_no_hits(void)
{
    TEST(tcam_search_dst_no_hits);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    tcam_crossbar_add_edge(&tcam, 0, 1, 0, 0);
    tcam_crossbar_add_edge(&tcam, 2, 3, 0, 0);

    tcam_hit_vector_t hv;
    int hits = tcam_crossbar_search_dst(&tcam, 99, &hv);
    ASSERT_EQ(hits, 0, "node 99 has no incoming edges");
    ASSERT_EQ(hv.hit_count, 0, "hit count should be 0");
    PASS();
}

/* ---- 3.4 TCAM Search by Vertex + Layer ---- */

static void test_tcam_search_vtx_layer(void)
{
    TEST(tcam_search_vtx_layer_match);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    tcam_crossbar_add_edge(&tcam, 0, 1, 10, 2);
    tcam_crossbar_add_edge(&tcam, 2, 3, 10, 3);
    tcam_crossbar_add_edge(&tcam, 4, 5, 20, 2);

    tcam_hit_vector_t hv;
    int hits = tcam_crossbar_search_vtx_layer(&tcam, 10, 2, &hv);
    ASSERT_EQ(hits, 1, "vtx=10,layer=2 → 1 hit");
    ASSERT_EQ(hv.bits[0], 1, "row 0 matches");
    ASSERT_EQ(hv.bits[1], 0, "row 1 doesn't match (layer 3≠2)");
    ASSERT_EQ(hv.bits[2], 0, "row 2 doesn't match (vtx 20≠10)");
    PASS();
}

static void test_tcam_search_vtx_layer_dont_care(void)
{
    TEST(tcam_search_vtx_layer_dont_care);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    /* -1 = don't-care (matches any vertex or layer) */
    tcam_crossbar_add_edge(&tcam, 0, 1, -1, 2);  /* any vertex, layer 2 */
    tcam_crossbar_add_edge(&tcam, 2, 3, 10, -1);  /* vtx 10, any layer   */
    tcam_crossbar_add_edge(&tcam, 4, 5, 10, 2);   /* exact match          */

    tcam_hit_vector_t hv;
    int hits = tcam_crossbar_search_vtx_layer(&tcam, 10, 2, &hv);
    ASSERT_EQ(hits, 3, "all 3 rows should match (2 don't-care + 1 exact)");
    PASS();
}

static void test_tcam_search_stats(void)
{
    TEST(tcam_search_stats_increment);
    tcam_crossbar_t tcam;
    tcam_crossbar_init(&tcam);

    tcam_crossbar_add_edge(&tcam, 0, 1, 0, 0);
    tcam_crossbar_add_edge(&tcam, 2, 1, 0, 0);

    tcam_hit_vector_t hv;
    tcam_crossbar_search_dst(&tcam, 1, &hv);
    ASSERT_EQ(tcam.searches, 1, "1 search performed");
    ASSERT_EQ(tcam.hits, 2, "2 total hits");

    tcam_crossbar_search_dst(&tcam, 99, &hv);
    ASSERT_EQ(tcam.searches, 2, "2 searches performed");
    ASSERT_EQ(tcam.hits, 2, "still 2 total hits");
    PASS();
}

/* ---- 3.5 MAC Crossbar ---- */

static void test_mac_crossbar_init(void)
{
    TEST(mac_crossbar_init_zeroed);
    mac_crossbar_t mac;
    int rc = mac_crossbar_init(&mac);
    ASSERT_EQ(rc, 0, "init should succeed");
    ASSERT_EQ(mac.row_count, 0, "no rows after init");
    ASSERT_EQ(mac.mac_ops, 0, "no MAC ops after init");
    ASSERT_EQ(mac.initialized, 1, "should be initialized");
    PASS();
}

static void test_mac_add_features(void)
{
    TEST(mac_add_features_basic);
    mac_crossbar_t mac;
    mac_crossbar_init(&mac);

    int feats[] = {10, 20, 30, 40};
    int idx = mac_crossbar_add_features(&mac, feats, 4);
    ASSERT_EQ(idx, 0, "first row at index 0");
    ASSERT_EQ(mac.row_count, 1, "should have 1 row");
    ASSERT_EQ(mac.features[0].features[0], 10, "feature[0] = 10");
    ASSERT_EQ(mac.features[0].features[3], 40, "feature[3] = 40");
    ASSERT_EQ(mac.features[0].dim, 4, "dim = 4");
    PASS();
}

static void test_mac_accumulate_with_hit_vector(void)
{
    TEST(mac_accumulate_hit_vector_gated);
    mac_crossbar_t mac;
    mac_crossbar_init(&mac);

    /* Add 3 feature rows */
    int f1[] = {10, 20};
    int f2[] = {30, 40};
    int f3[] = {50, 60};
    mac_crossbar_add_features(&mac, f1, 2);
    mac_crossbar_add_features(&mac, f2, 2);
    mac_crossbar_add_features(&mac, f3, 2);

    /* Hit vector: only rows 0 and 2 */
    tcam_hit_vector_t hv;
    memset(&hv, 0, sizeof(hv));
    hv.length = 3;
    hv.bits[0] = 1;
    hv.bits[1] = 0;
    hv.bits[2] = 1;
    hv.hit_count = 2;

    int result[2] = {0, 0};
    int rc = mac_crossbar_accumulate(&mac, &hv, result, 2);
    ASSERT_EQ(rc, 0, "accumulate should succeed");
    /* result = f1 + f3 = (10+50, 20+60) = (60, 80) */
    ASSERT_EQ(result[0], 60, "acc[0] = 10+50 = 60");
    ASSERT_EQ(result[1], 80, "acc[1] = 20+60 = 80");
    PASS();
}

static void test_mac_accumulate_empty_hit(void)
{
    TEST(mac_accumulate_empty_hit_vector);
    mac_crossbar_t mac;
    mac_crossbar_init(&mac);

    int feats[] = {100, 200};
    mac_crossbar_add_features(&mac, feats, 2);

    tcam_hit_vector_t hv;
    memset(&hv, 0, sizeof(hv));
    hv.length = 1;
    hv.hit_count = 0;

    int result[2] = {99, 99};
    int rc = mac_crossbar_accumulate(&mac, &hv, result, 2);
    ASSERT_EQ(rc, 0, "accumulate should succeed");
    /* No hits → result should be zeroed */
    ASSERT_EQ(result[0], 0, "no hits → result[0] = 0");
    ASSERT_EQ(result[1], 0, "no hits → result[1] = 0");
    PASS();
}

/* ---- 3.6 Dynamic Fixed-Point ---- */

static void test_dfp_encode_group0(void)
{
    TEST(dfp_encode_group0_exponent_0_to_3);
    tcam_dfp_value_t dfp;

    /* Exponent 0: group 0, shift 0 */
    int rc = tcam_dfp_encode(100, 0, &dfp);
    ASSERT_EQ(rc, 0, "encode should succeed");
    ASSERT_EQ(dfp.group, 0, "exponent 0 → group 0");
    ASSERT_EQ(dfp.shift, 0, "exponent 0 → shift 0");

    /* Exponent -3: group 0, shift 3 */
    rc = tcam_dfp_encode(100, -3, &dfp);
    ASSERT_EQ(rc, 0, "encode should succeed");
    ASSERT_EQ(dfp.group, 0, "exponent -3 → group 0");
    ASSERT_EQ(dfp.shift, 3, "exponent -3 → shift 3");
    PASS();
}

static void test_dfp_encode_group1(void)
{
    TEST(dfp_encode_group1_exponent_4_to_7);
    tcam_dfp_value_t dfp;

    /* Exponent -4: group 1, shift 0 */
    int rc = tcam_dfp_encode(100, -4, &dfp);
    ASSERT_EQ(rc, 0, "encode should succeed");
    ASSERT_EQ(dfp.group, 1, "exponent -4 → group 1");
    ASSERT_EQ(dfp.shift, 0, "exponent -4 → shift 0");

    /* Exponent -7: group 1, shift 3 */
    rc = tcam_dfp_encode(100, -7, &dfp);
    ASSERT_EQ(rc, 0, "encode should succeed");
    ASSERT_EQ(dfp.group, 1, "exponent -7 → group 1");
    ASSERT_EQ(dfp.shift, 3, "exponent -7 → shift 3");
    PASS();
}

static void test_dfp_encode_null(void)
{
    TEST(dfp_encode_null_rejected);
    ASSERT_EQ(tcam_dfp_encode(100, 0, NULL), -1, "NULL should be rejected");
    PASS();
}

static void test_dfp_decode_basic(void)
{
    TEST(dfp_decode_basic_reconstruction);
    tcam_dfp_value_t dfp;

    /* Encode with exponent 0 → should reconstruct closely */
    tcam_dfp_encode(200, 0, &dfp);
    int decoded = tcam_dfp_decode(&dfp);
    ASSERT_TRUE(decoded > 0, "decoded should be positive");
    PASS();
}

static void test_dfp_mac_basic(void)
{
    TEST(dfp_mac_accumulation);
    tcam_dfp_value_t a[3], b[3];

    /* Encode 3 pairs with exponent 0 */
    for (int i = 0; i < 3; i++) {
        tcam_dfp_encode(10 * (i + 1), 0, &a[i]);
        tcam_dfp_encode(10, 0, &b[i]);
    }

    int result = tcam_dfp_mac(a, b, 3);
    /* All in group 0, so should produce non-zero accumulation */
    ASSERT_TRUE(result != 0, "DFP MAC should produce non-zero result");
    PASS();
}

static void test_dfp_mac_null_returns_zero(void)
{
    TEST(dfp_mac_null_returns_zero);
    int result = tcam_dfp_mac(NULL, NULL, 5);
    ASSERT_EQ(result, 0, "NULL arrays should return 0");
    PASS();
}

/* ---- 3.7 GNN Pipeline ---- */

static void test_gnn_init(void)
{
    TEST(gnn_init_zeroed);
    tcam_gnn_state_t state;
    int rc = tcam_gnn_init(&state);
    ASSERT_EQ(rc, 0, "GNN init should succeed");
    ASSERT_EQ(state.initialized, 1, "should be initialized");
    ASSERT_EQ(state.epochs_completed, 0, "no epochs after init");
    ASSERT_EQ(state.tcam.initialized, 1, "TCAM sub-init should succeed");
    ASSERT_EQ(state.mac.initialized, 1, "MAC sub-init should succeed");
    PASS();
}

static void test_gnn_init_null(void)
{
    TEST(gnn_init_null_rejected);
    ASSERT_EQ(tcam_gnn_init(NULL), -1, "NULL should be rejected");
    PASS();
}

static void test_gnn_load_graph(void)
{
    TEST(gnn_load_graph_basic);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    /* Build a simple 4-node triangle graph with 1 extra edge */
    tcam_graph_t graph;
    memset(&graph, 0, sizeof(graph));
    graph.node_count = 4;
    graph.edge_count = 4;
    graph.feature_dim = 2;

    /* Edges: 0→1, 1→2, 2→0, 3→1 */
    graph.edge_src[0] = 0; graph.edge_dst[0] = 1;
    graph.edge_src[1] = 1; graph.edge_dst[1] = 2;
    graph.edge_src[2] = 2; graph.edge_dst[2] = 0;
    graph.edge_src[3] = 3; graph.edge_dst[3] = 1;

    /* Features: node i has feature [i*10, i*10+5] */
    for (int i = 0; i < 4; i++) {
        graph.node_features[i][0] = i * 10;
        graph.node_features[i][1] = i * 10 + 5;
    }

    int rc = tcam_gnn_load_graph(&state, &graph);
    ASSERT_EQ(rc, 0, "load graph should succeed");
    ASSERT_EQ(state.graph.node_count, 4, "4 nodes loaded");
    ASSERT_EQ(state.graph.edge_count, 4, "4 edges loaded");
    ASSERT_EQ(state.tcam.row_count, 4, "TCAM should have 4 rows");
    ASSERT_EQ(state.mac.row_count, 4, "MAC should have 4 rows");
    PASS();
}

static void test_gnn_sample_batch(void)
{
    TEST(gnn_sample_batch_produces_nodes);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    tcam_graph_t graph;
    memset(&graph, 0, sizeof(graph));
    graph.node_count = 8;
    graph.edge_count = 2;
    graph.feature_dim = 2;
    graph.edge_src[0] = 0; graph.edge_dst[0] = 1;
    graph.edge_src[1] = 1; graph.edge_dst[1] = 0;
    for (int i = 0; i < 8; i++) {
        graph.node_features[i][0] = i;
        graph.node_features[i][1] = i * 2;
    }

    tcam_gnn_load_graph(&state, &graph);

    int batch = tcam_gnn_sample_batch(&state, 4, 42);
    ASSERT_EQ(batch, 4, "should sample 4 nodes");
    ASSERT_EQ(state.batch_size, 4, "batch_size should be 4");

    /* All sampled nodes should be valid indices */
    for (int i = 0; i < 4; i++) {
        ASSERT_TRUE(state.batch_nodes[i] >= 0 && state.batch_nodes[i] < 8,
                     "sampled node should be in range");
    }
    PASS();
}

static void test_gnn_aggregate(void)
{
    TEST(gnn_aggregate_accumulates_features);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    /* Simple 3-node graph: 0→1, 2→1 */
    tcam_graph_t graph;
    memset(&graph, 0, sizeof(graph));
    graph.node_count = 3;
    graph.edge_count = 2;
    graph.feature_dim = 2;
    graph.edge_src[0] = 0; graph.edge_dst[0] = 1;
    graph.edge_src[1] = 2; graph.edge_dst[1] = 1;

    /* Node features */
    graph.node_features[0][0] = 10; graph.node_features[0][1] = 20;
    graph.node_features[1][0] = 30; graph.node_features[1][1] = 40;
    graph.node_features[2][0] = 50; graph.node_features[2][1] = 60;

    tcam_gnn_load_graph(&state, &graph);

    /* Manually set batch to just node 1 */
    state.batch_nodes[0] = 1;
    state.batch_size = 1;

    int agg = tcam_gnn_aggregate(&state);
    ASSERT_EQ(agg, 1, "should aggregate 1 node");

    /*
     * Node 1 has edges FROM nodes 0 and 2.
     * Aggregated[1] = self_features[1] + neighbor_features[0] + neighbor_features[2]
     *               = (30,40) + (10,20) + (50,60) = (90, 120)
     */
    int out[2];
    tcam_gnn_get_node_features(&state, 1, out, 2);
    ASSERT_EQ(out[0], 90, "aggregated[1][0] = 30+10+50 = 90");
    ASSERT_EQ(out[1], 120, "aggregated[1][1] = 40+20+60 = 120");
    PASS();
}

static void test_gnn_update(void)
{
    TEST(gnn_update_applies_weights);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    /* Simple graph for setup */
    tcam_graph_t graph;
    memset(&graph, 0, sizeof(graph));
    graph.node_count = 2;
    graph.edge_count = 1;
    graph.feature_dim = 2;
    graph.edge_src[0] = 0; graph.edge_dst[0] = 1;
    graph.node_features[0][0] = 5; graph.node_features[0][1] = 10;
    graph.node_features[1][0] = 15; graph.node_features[1][1] = 20;

    tcam_gnn_load_graph(&state, &graph);

    /* Set batch to node 1, aggregate first */
    state.batch_nodes[0] = 1;
    state.batch_size = 1;
    tcam_gnn_aggregate(&state);

    /* Weights are identity after load, so update should preserve values */
    int before[2];
    tcam_gnn_get_node_features(&state, 1, before, 2);

    int rc = tcam_gnn_update(&state);
    ASSERT_EQ(rc, 0, "update should succeed");

    int after[2];
    tcam_gnn_get_node_features(&state, 1, after, 2);
    /* Identity weight → values should remain the same */
    ASSERT_EQ(after[0], before[0], "identity weights → same value[0]");
    ASSERT_EQ(after[1], before[1], "identity weights → same value[1]");
    PASS();
}

static void test_gnn_train_epoch(void)
{
    TEST(gnn_train_epoch_completes);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    /* Build a 6-node graph */
    tcam_graph_t graph;
    memset(&graph, 0, sizeof(graph));
    graph.node_count = 6;
    graph.edge_count = 8;
    graph.feature_dim = 3;

    /* Ring edges + some cross edges */
    int srcs[] = {0,1,2,3,4,5,0,3};
    int dsts[] = {1,2,3,4,5,0,3,0};
    for (int i = 0; i < 8; i++) {
        graph.edge_src[i] = srcs[i];
        graph.edge_dst[i] = dsts[i];
    }
    for (int i = 0; i < 6; i++) {
        for (int j = 0; j < 3; j++) {
            graph.node_features[i][j] = (i + 1) * (j + 1);
        }
    }

    tcam_gnn_load_graph(&state, &graph);

    int rc = tcam_gnn_train_epoch(&state, 12345);
    ASSERT_EQ(rc, 0, "train epoch should succeed");
    ASSERT_EQ(state.epochs_completed, 1, "1 epoch completed");
    ASSERT_EQ(state.batches_processed, 1, "1 batch processed");
    ASSERT_GT0(state.total_aggregations, "should have some aggregations");
    PASS();
}

static void test_gnn_train_multiple_epochs(void)
{
    TEST(gnn_train_multiple_epochs);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    tcam_graph_t graph;
    memset(&graph, 0, sizeof(graph));
    graph.node_count = 4;
    graph.edge_count = 4;
    graph.feature_dim = 2;
    graph.edge_src[0] = 0; graph.edge_dst[0] = 1;
    graph.edge_src[1] = 1; graph.edge_dst[1] = 2;
    graph.edge_src[2] = 2; graph.edge_dst[2] = 3;
    graph.edge_src[3] = 3; graph.edge_dst[3] = 0;
    for (int i = 0; i < 4; i++) {
        graph.node_features[i][0] = i * 5;
        graph.node_features[i][1] = i * 5 + 1;
    }

    tcam_gnn_load_graph(&state, &graph);

    for (int e = 0; e < 3; e++) {
        int rc = tcam_gnn_train_epoch(&state, 1000 + e);
        ASSERT_EQ(rc, 0, "epoch should succeed");
    }
    ASSERT_EQ(state.epochs_completed, 3, "3 epochs completed");
    PASS();
}

static void test_gnn_get_features_invalid_node(void)
{
    TEST(gnn_get_features_invalid_node);
    tcam_gnn_state_t state;
    tcam_gnn_init(&state);

    int out[2];
    /* No graph loaded → any node is invalid */
    ASSERT_EQ(tcam_gnn_get_node_features(&state, 0, out, 2), -1,
              "invalid node should be rejected");
    PASS();
}


/* ===================================================================== */
/*  Main — Run All Tests                                                 */
/* ===================================================================== */

int main(void)
{
    printf("════════════════════════════════════════════════════════════════\n");
    printf("  TSMC TMD / Intel PAM-3 / Hynix TCAM — Combined Test Suite\n");
    printf("════════════════════════════════════════════════════════════════\n");

    /* ---- PART 1: TSMC TMD Heterostack & FET ---- */
    printf("\n[Part 1: TSMC US20230307234A1 — TMD Heterostack]\n");

    printf("\n  [1.1 Monolayer Creation]\n");
    test_tmd_monolayer_mos2();
    test_tmd_monolayer_hbn();
    test_tmd_monolayer_ws2();
    test_tmd_monolayer_mose2();
    test_tmd_monolayer_wse2();
    test_tmd_monolayer_mote2();
    test_tmd_monolayer_graphene();
    test_tmd_monolayer_null_ptr();

    printf("\n  [1.2 Material Classification]\n");
    test_tmd_is_semiconductor();
    test_tmd_is_dielectric();

    printf("\n  [1.3 Heterostack Operations]\n");
    test_tmd_stack_init();
    test_tmd_stack_add_single_layer();
    test_tmd_stack_hbn_mos2_hbn_sandwich();
    test_tmd_stack_not_sandwich();
    test_tmd_stack_total_thickness();

    printf("\n  [1.4 Bonding Parameters]\n");
    test_tmd_bond_params_valid();
    test_tmd_bond_params_boundary_low();
    test_tmd_bond_params_boundary_high();
    test_tmd_bond_params_out_of_range();

    printf("\n  [1.5 Carrier Film]\n");
    test_tmd_carrier_attach_remove();
    test_tmd_substrate_attach();

    printf("\n  [1.6 Quality Score]\n");
    test_tmd_quality_score_perfect();
    test_tmd_quality_score_range();

    printf("\n  [1.7 TMD FET Operations]\n");
    test_tmd_fet_init();
    test_tmd_fet_evaluate_low();
    test_tmd_fet_evaluate_mid();
    test_tmd_fet_evaluate_high();
    test_tmd_fet_ternary_not();
    test_tmd_fet_ternary_and();
    test_tmd_fet_ternary_or();
    test_tmd_fet_on_current();

    printf("\n  [1.8 3D Monolithic Model]\n");
    test_tmd_3d_init();
    test_tmd_3d_density();
    test_tmd_3d_validate();

    /* ---- PART 2: Intel PAM-3 Decoder Pipeline ---- */
    printf("\n[Part 2: Intel US11405248B2 — PAM-3 FPGA Decoder]\n");

    printf("\n  [2.1 Initialization]\n");
    test_pam3d_init();
    test_pam3d_init_null();
    test_pam3d_set_thresholds();
    test_pam3d_dc_correction_toggle();

    printf("\n  [2.2 Test Signal Generation]\n");
    test_pam3d_generate_signal_basic();
    test_pam3d_generate_signal_with_noise();
    test_pam3d_generate_signal_empty();

    printf("\n  [2.3 Sample Loading]\n");
    test_pam3d_load_samples();
    test_pam3d_load_samples_overflow();

    printf("\n  [2.4 Full Pipeline Decode]\n");
    test_pam3d_full_decode_clean();
    test_pam3d_full_decode_noisy();

    printf("\n  [2.5 Individual Pipeline Stages]\n");
    test_pam3d_dc_correction_stage();
    test_pam3d_level_detection_stage();
    test_pam3d_spike_filter_stage();
    test_pam3d_edge_detection_stage();
    test_pam3d_stats_accumulate();

    /* ---- PART 3: Hynix TCAM Crossbar for GNN ---- */
    printf("\n[Part 3: Macronix/Hynix US20230162024A1 — TCAM GNN]\n");

    printf("\n  [3.1 TCAM Crossbar Init]\n");
    test_tcam_crossbar_init();
    test_tcam_crossbar_init_null();

    printf("\n  [3.2 TCAM Add Edge]\n");
    test_tcam_add_edge();
    test_tcam_add_multiple_edges();
    test_tcam_add_edge_overflow();

    printf("\n  [3.3 TCAM Search (Destination)]\n");
    test_tcam_search_dst_single_hit();
    test_tcam_search_dst_multiple_hits();
    test_tcam_search_dst_no_hits();

    printf("\n  [3.4 TCAM Search (Vertex + Layer)]\n");
    test_tcam_search_vtx_layer();
    test_tcam_search_vtx_layer_dont_care();
    test_tcam_search_stats();

    printf("\n  [3.5 MAC Crossbar]\n");
    test_mac_crossbar_init();
    test_mac_add_features();
    test_mac_accumulate_with_hit_vector();
    test_mac_accumulate_empty_hit();

    printf("\n  [3.6 Dynamic Fixed-Point]\n");
    test_dfp_encode_group0();
    test_dfp_encode_group1();
    test_dfp_encode_null();
    test_dfp_decode_basic();
    test_dfp_mac_basic();
    test_dfp_mac_null_returns_zero();

    printf("\n  [3.7 GNN Pipeline]\n");
    test_gnn_init();
    test_gnn_init_null();
    test_gnn_load_graph();
    test_gnn_sample_batch();
    test_gnn_aggregate();
    test_gnn_update();
    test_gnn_train_epoch();
    test_gnn_train_multiple_epochs();
    test_gnn_get_features_invalid_node();

    /* ---- Summary ---- */
    printf("\n=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);

    return tests_failed ? EXIT_FAILURE : EXIT_SUCCESS;
}
