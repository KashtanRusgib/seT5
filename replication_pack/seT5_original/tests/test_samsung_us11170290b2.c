/**
 * @file test_samsung_us11170290b2.c
 * @brief Comprehensive test suite for Samsung US11170290B2 NAND inference HAL
 *
 * Tests every layer of the Samsung hardware abstraction:
 *   - Weight encoding and unit synapse programming
 *   - Voltage pattern encoding for ternary inputs
 *   - Cell conductivity model (Vread / Vpass)
 *   - Unit synapse evaluation (XNOR of input and weight)
 *   - Zero Input Detection (ZID) — count and bitmap
 *   - BNN dot-product (Eq. 1): P = 2·CNT − S
 *   - TBN dot-product (Eq. 2): P = 2·CNT − (S − Z)
 *   - Matrix-vector multiplication
 *   - Activation functions (sign, ternary)
 *   - Multi-layer DNN inference
 *   - HAL lifecycle (init / set mode / shutdown)
 *   - Parallelism configuration
 *   - Weight programming / readback
 *
 * Every ASSERT checks a computed value against an independently
 * verifiable expected value — no tautologies.
 *
 * Build:
 *   gcc -Wall -Wextra -Iinclude -o test_samsung_us11170290b2 \
 *       tests/test_samsung_us11170290b2.c \
 *       src/samsung_tbn.c src/samsung_hal.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "set5/samsung_us11170290b2.h"
#include "set5/samsung_nand.h"
#include "set5/samsung_tbn.h"

/* ===================================================================== */
/* Test Infrastructure                                                   */
/* ===================================================================== */

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name)                                                    \
    do {                                                              \
        printf("  %-55s ", #name);                                    \
        fflush(stdout);                                               \
    } while(0)

#define PASS()                                                        \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

#define FAIL(msg)                                                     \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

/* ===================================================================== */
/* 1. Weight Encoding Tests                                              */
/* ===================================================================== */

static void test_weight_valid(void)
{
    TEST(weight_valid_pos_neg);

    ASSERT_TRUE(ss_weight_valid(SS_WEIGHT_POS), "+1 should be valid weight");
    ASSERT_TRUE(ss_weight_valid(SS_WEIGHT_NEG), "-1 should be valid weight");
    ASSERT_TRUE(!ss_weight_valid(0), "0 should not be valid weight");

    PASS();
}

static void test_synapse_program_pos(void)
{
    TEST(synapse_program_weight_pos);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_POS);
    ASSERT_EQ(s.fg1, SS_CELL_ERASED,     "W=+1: FG1 should be erased");
    ASSERT_EQ(s.fg2, SS_CELL_PROGRAMMED,  "W=+1: FG2 should be programmed");

    PASS();
}

static void test_synapse_program_neg(void)
{
    TEST(synapse_program_weight_neg);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_NEG);
    ASSERT_EQ(s.fg1, SS_CELL_PROGRAMMED, "W=-1: FG1 should be programmed");
    ASSERT_EQ(s.fg2, SS_CELL_ERASED,     "W=-1: FG2 should be erased");

    PASS();
}

static void test_synapse_read_weight(void)
{
    TEST(synapse_read_weight_roundtrip);

    ss_unit_synapse_t sp = ss_synapse_program(SS_WEIGHT_POS);
    ASSERT_EQ(ss_synapse_read_weight(sp), SS_WEIGHT_POS, "read +1 weight");

    ss_unit_synapse_t sn = ss_synapse_program(SS_WEIGHT_NEG);
    ASSERT_EQ(ss_synapse_read_weight(sn), SS_WEIGHT_NEG, "read -1 weight");

    PASS();
}

/* ===================================================================== */
/* 2. Voltage Pattern Encoding Tests                                     */
/* ===================================================================== */

static void test_encode_input_neg(void)
{
    TEST(encode_input_negative_one);

    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_NEG);
    ASSERT_EQ(vp.v1, SS_V_PASS, "Input -1: V1 should be Vpass");
    ASSERT_EQ(vp.v2, SS_V_READ, "Input -1: V2 should be Vread");

    PASS();
}

static void test_encode_input_pos(void)
{
    TEST(encode_input_positive_one);

    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_POS);
    ASSERT_EQ(vp.v1, SS_V_READ, "Input +1: V1 should be Vread");
    ASSERT_EQ(vp.v2, SS_V_PASS, "Input +1: V2 should be Vpass");

    PASS();
}

static void test_encode_input_zero(void)
{
    TEST(encode_input_zero);

    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_ZERO);
    ASSERT_EQ(vp.v1, SS_V_READ, "Input 0: V1 should be Vread");
    ASSERT_EQ(vp.v2, SS_V_READ, "Input 0: V2 should be Vread");

    PASS();
}

static void test_is_zero_input(void)
{
    TEST(is_zero_input_detection);

    ss_voltage_pattern_t vp_zero = ss_encode_input(SS_INPUT_ZERO);
    ASSERT_EQ(ss_is_zero_input(vp_zero), 1, "Zero input should be detected");

    ss_voltage_pattern_t vp_pos = ss_encode_input(SS_INPUT_POS);
    ASSERT_EQ(ss_is_zero_input(vp_pos), 0, "+1 should not be zero");

    ss_voltage_pattern_t vp_neg = ss_encode_input(SS_INPUT_NEG);
    ASSERT_EQ(ss_is_zero_input(vp_neg), 0, "-1 should not be zero");

    PASS();
}

/* ===================================================================== */
/* 3. Cell Conductivity Tests                                            */
/* ===================================================================== */

static void test_cell_conducts_erased_vread(void)
{
    TEST(cell_erased_at_vread_conducts);

    ASSERT_EQ(ss_cell_conducts(SS_CELL_ERASED, SS_V_READ), 1,
              "Erased cell should conduct at Vread");
    PASS();
}

static void test_cell_programmed_vread(void)
{
    TEST(cell_programmed_at_vread_blocks);

    ASSERT_EQ(ss_cell_conducts(SS_CELL_PROGRAMMED, SS_V_READ), 0,
              "Programmed cell should NOT conduct at Vread");
    PASS();
}

static void test_cell_any_vpass(void)
{
    TEST(any_cell_at_vpass_conducts);

    ASSERT_EQ(ss_cell_conducts(SS_CELL_ERASED, SS_V_PASS), 1,
              "Erased at Vpass should conduct");
    ASSERT_EQ(ss_cell_conducts(SS_CELL_PROGRAMMED, SS_V_PASS), 1,
              "Programmed at Vpass should conduct");
    PASS();
}

/* ===================================================================== */
/* 4. Unit Synapse Evaluation (all 6 cases from patent FIGS 12-15)       */
/* ===================================================================== */

/*
 * Patent Cases (using balanced ternary):
 *
 * Case 1: W=+1, I=+1  → FG1=E,FG2=P; V1=Vread,V2=Vpass
 *         C1=E@Vread=1, C2=P@Vpass=1 → conducts (match = +1)
 *
 * Case 2: W=+1, I=-1  → FG1=E,FG2=P; V1=Vpass,V2=Vread
 *         C1=E@Vpass=1, C2=P@Vread=0 → blocks (mismatch = -1)
 *
 * Case 3: W=-1, I=+1  → FG1=P,FG2=E; V1=Vread,V2=Vpass
 *         C1=P@Vread=0, C2=E@Vpass=1 → blocks (mismatch = -1)
 *
 * Case 4: W=-1, I=-1  → FG1=P,FG2=E; V1=Vpass,V2=Vread
 *         C1=P@Vpass=1, C2=E@Vread=1 → conducts (match = +1)
 *
 * Case 5: W=+1, I=0   → FG1=E,FG2=P; V1=Vread,V2=Vread
 *         C1=E@Vread=1, C2=P@Vread=0 → blocks (-1, excluded by ZID)
 *
 * Case 6: W=-1, I=0   → FG1=P,FG2=E; V1=Vread,V2=Vread
 *         C1=P@Vread=0, C2=E@Vread=1 → blocks (-1, excluded by ZID)
 */

static void test_synapse_case1(void)
{
    TEST(synapse_W+1_I+1_conducts);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_POS);
    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_POS);
    ASSERT_EQ(ss_synapse_eval(s, vp), 1, "W=+1,I=+1 should conduct");

    PASS();
}

static void test_synapse_case2(void)
{
    TEST(synapse_W+1_I-1_blocks);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_POS);
    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_NEG);
    ASSERT_EQ(ss_synapse_eval(s, vp), 0, "W=+1,I=-1 should block");

    PASS();
}

static void test_synapse_case3(void)
{
    TEST(synapse_W-1_I+1_blocks);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_NEG);
    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_POS);
    ASSERT_EQ(ss_synapse_eval(s, vp), 0, "W=-1,I=+1 should block");

    PASS();
}

static void test_synapse_case4(void)
{
    TEST(synapse_W-1_I-1_conducts);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_NEG);
    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_NEG);
    ASSERT_EQ(ss_synapse_eval(s, vp), 1, "W=-1,I=-1 should conduct");

    PASS();
}

static void test_synapse_case5(void)
{
    TEST(synapse_W+1_I0_blocks);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_POS);
    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_ZERO);
    ASSERT_EQ(ss_synapse_eval(s, vp), 0, "W=+1,I=0 should block");

    PASS();
}

static void test_synapse_case6(void)
{
    TEST(synapse_W-1_I0_blocks);

    ss_unit_synapse_t s = ss_synapse_program(SS_WEIGHT_NEG);
    ss_voltage_pattern_t vp = ss_encode_input(SS_INPUT_ZERO);
    ASSERT_EQ(ss_synapse_eval(s, vp), 0, "W=-1,I=0 should block");

    PASS();
}

/* ===================================================================== */
/* 5. ZID (Zero Input Detection) Tests                                   */
/* ===================================================================== */

static void test_zid_count_no_zeros(void)
{
    TEST(zid_count_zeros_binary_only);

    ss_input_t inputs[] = {1, -1, 1, -1, 1};
    ASSERT_EQ(ss_zid_count_zeros(inputs, 5), 0, "No zeros in binary input");

    PASS();
}

static void test_zid_count_some_zeros(void)
{
    TEST(zid_count_with_ternary_zeros);

    ss_input_t inputs[] = {1, 0, -1, 0, 1, 0, -1};
    ASSERT_EQ(ss_zid_count_zeros(inputs, 7), 3, "Should detect 3 zeros");

    PASS();
}

static void test_zid_count_all_zeros(void)
{
    TEST(zid_count_all_inputs_zero);

    ss_input_t inputs[] = {0, 0, 0, 0};
    ASSERT_EQ(ss_zid_count_zeros(inputs, 4), 4, "All 4 should be zeros");

    PASS();
}

static void test_zid_bitmap_pattern(void)
{
    TEST(zid_bitmap_correct_bits);

    ss_input_t inputs[] = {1, 0, -1, 0, 1, -1, 0, 1};
    uint32_t bitmap[1];
    ss_zid_bitmap(inputs, 8, bitmap);

    /* Zeros at positions 1, 3, 6 → bits 1, 3, 6 set */
    uint32_t expected = (1u << 1) | (1u << 3) | (1u << 6);
    ASSERT_EQ(bitmap[0], expected, "Bitmap should have bits 1,3,6 set");

    PASS();
}

static void test_zid_bitmap_empty(void)
{
    TEST(zid_bitmap_no_zeros);

    ss_input_t inputs[] = {1, -1, 1, -1};
    uint32_t bitmap[1];
    ss_zid_bitmap(inputs, 4, bitmap);
    ASSERT_EQ(bitmap[0], 0u, "Bitmap should be empty for binary inputs");

    PASS();
}

/* ===================================================================== */
/* 6. BNN Dot-Product Tests (Eq. 1: P = 2·CNT − S)                      */
/* ===================================================================== */

static void test_bnn_dot_all_match(void)
{
    TEST(bnn_dot_product_all_match);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_BNN);

    /* W = [+1,+1,+1,+1], I = [+1,+1,+1,+1]
     * All match → CNT=4, P = 2*4 - 4 = 4 */
    ss_weight_t w[] = {1, 1, 1, 1};
    ss_input_t  x[] = {1, 1, 1, 1};

    ss_dot_result_t r = ss_dot_bnn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, 4, "All match: dot should be 4");
    ASSERT_EQ(r.cnt_out, 4, "All match: CNT should be 4");
    ASSERT_EQ(r.z_count, 0, "BNN: no zeros expected");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_bnn_dot_all_mismatch(void)
{
    TEST(bnn_dot_product_all_mismatch);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* W = [+1,+1,+1,+1], I = [-1,-1,-1,-1]
     * All mismatch → CNT=0, P = 2*0 - 4 = -4 */
    ss_weight_t w[] = {1, 1, 1, 1};
    ss_input_t  x[] = {-1, -1, -1, -1};

    ss_dot_result_t r = ss_dot_bnn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, -4, "All mismatch: dot should be -4");
    ASSERT_EQ(r.cnt_out, 0, "All mismatch: CNT should be 0");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_bnn_dot_mixed(void)
{
    TEST(bnn_dot_product_mixed);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* W = [+1,-1,+1,-1], I = [+1,+1,-1,-1]
     * Match at pos 0 (1*1) and pos 3 (-1*-1): CNT=2
     * P = 2*2 - 4 = 0
     * Real dot: (+1)(+1) + (-1)(+1) + (+1)(-1) + (-1)(-1) = 1-1-1+1 = 0 ✓ */
    ss_weight_t w[] = {1, -1, 1, -1};
    ss_input_t  x[] = {1,  1, -1, -1};

    ss_dot_result_t r = ss_dot_bnn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, 0, "Mixed: dot should be 0");
    ASSERT_EQ(r.cnt_out, 2, "Mixed: CNT should be 2");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_bnn_dot_single(void)
{
    TEST(bnn_dot_product_size_1);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    ss_weight_t w_pos[] = {1};
    ss_weight_t w_neg[] = {-1};
    ss_input_t  x_pos[] = {1};
    ss_input_t  x_neg[] = {-1};

    /* W=+1, I=+1 → CNT=1, P=2*1-1=1 */
    ss_dot_result_t r1 = ss_dot_bnn(&hal, w_pos, x_pos, 1);
    ASSERT_EQ(r1.dot_product, 1, "1*1 should be 1");

    /* W=+1, I=-1 → CNT=0, P=2*0-1=-1 */
    ss_dot_result_t r2 = ss_dot_bnn(&hal, w_pos, x_neg, 1);
    ASSERT_EQ(r2.dot_product, -1, "1*(-1) should be -1");

    /* W=-1, I=+1 → CNT=0, P=2*0-1=-1 */
    ss_dot_result_t r3 = ss_dot_bnn(&hal, w_neg, x_pos, 1);
    ASSERT_EQ(r3.dot_product, -1, "(-1)*1 should be -1");

    /* W=-1, I=-1 → CNT=1, P=2*1-1=1 */
    ss_dot_result_t r4 = ss_dot_bnn(&hal, w_neg, x_neg, 1);
    ASSERT_EQ(r4.dot_product, 1, "(-1)*(-1) should be 1");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 7. TBN Dot-Product Tests (Eq. 2: P = 2·CNT − (S − Z))               */
/* ===================================================================== */

static void test_tbn_dot_no_zeros(void)
{
    TEST(tbn_dot_no_zeros_matches_bnn);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* Without zeros, TBN should give same result as BNN */
    ss_weight_t w[] = {1, -1, 1, -1};
    ss_input_t  x[] = {1, -1, -1, 1};
    /* Match at 0 (1,1), 1 (-1,-1): CNT=2, Z=0
     * P = 2*2 - (4-0) = 0
     * Real dot: 1*1 + (-1)(-1) + 1(-1) + (-1)(1) = 1+1-1-1 = 0 ✓ */

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, 0, "TBN without zeros should match BNN");
    ASSERT_EQ(r.z_count, 0, "Z should be 0");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_tbn_dot_with_zeros(void)
{
    TEST(tbn_dot_with_zero_inputs);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* W = [+1, -1, +1, -1], I = [+1, 0, 0, -1]
     * Position 0: W=+1,I=+1 → match, CNT++      (CNT=1)
     * Position 1: I=0 → ZID detects, skip        (Z=1)
     * Position 2: I=0 → ZID detects, skip        (Z=2)
     * Position 3: W=-1,I=-1 → match, CNT++       (CNT=2)
     *
     * S=4, Z=2, S_eff=2, CNT=2
     * P = 2*2 - (4-2) = 4 - 2 = 2
     *
     * True dot: (+1)(+1) + (-1)(0) + (+1)(0) + (-1)(-1) = 1+0+0+1 = 2 ✓ */
    ss_weight_t w[] = {1, -1, 1, -1};
    ss_input_t  x[] = {1,  0, 0, -1};

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, 2, "TBN with zeros: dot should be 2");
    ASSERT_EQ(r.z_count, 2, "Should detect 2 zeros");
    ASSERT_EQ(r.cnt_out, 2, "CNT should be 2 (both non-zero match)");
    ASSERT_EQ(r.s_effective, 2, "S_eff should be S-Z=2");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_tbn_dot_all_zeros(void)
{
    TEST(tbn_dot_all_zero_inputs);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* All inputs zero → Z=4, CNT=0, P = 2*0 - (4-4) = 0
     * True dot: +1*0 + -1*0 + +1*0 + -1*0 = 0 ✓ */
    ss_weight_t w[] = {1, -1, 1, -1};
    ss_input_t  x[] = {0,  0, 0,  0};

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, 0, "All-zero input: dot should be 0");
    ASSERT_EQ(r.z_count, 4, "All 4 inputs are zero");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_tbn_dot_single_zero(void)
{
    TEST(tbn_dot_one_zero_in_middle);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* W = [+1, +1, +1], I = [+1, 0, -1]
     * Pos 0: match (+1,+1), CNT=1
     * Pos 1: zero, skip, Z=1
     * Pos 2: mismatch (+1,-1), CNT still 1
     * P = 2*1 - (3-1) = 2 - 2 = 0
     * True: 1*1 + 1*0 + 1*(-1) = 1+0-1 = 0 ✓ */
    ss_weight_t w[] = {1, 1, 1};
    ss_input_t  x[] = {1, 0, -1};

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 3);
    ASSERT_EQ(r.dot_product, 0, "One zero: dot should be 0");
    ASSERT_EQ(r.z_count, 1, "One zero detected");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_tbn_dot_asymmetric(void)
{
    TEST(tbn_dot_asymmetric_weights);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* W = [+1, +1, -1, -1, +1], I = [+1, 0, -1, 0, +1]
     * Pos 0: W=+1,I=+1 → match       CNT=1
     * Pos 1: I=0 → skip               Z=1
     * Pos 2: W=-1,I=-1 → match        CNT=2
     * Pos 3: I=0 → skip               Z=2
     * Pos 4: W=+1,I=+1 → match        CNT=3
     *
     * S=5, Z=2, S_eff=3, P = 2*3 - 3 = 3
     * True: 1 + 0 + 1 + 0 + 1 = 3 ✓ */
    ss_weight_t w[] = {1, 1, -1, -1, 1};
    ss_input_t  x[] = {1, 0, -1,  0, 1};

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 5);
    ASSERT_EQ(r.dot_product, 3, "Asymmetric: dot should be 3");
    ASSERT_EQ(r.z_count, 2, "Should detect 2 zeros");
    ASSERT_EQ(r.cnt_out, 3, "3 non-zero matches");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_tbn_dot_negative_result(void)
{
    TEST(tbn_dot_negative_result);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* W = [+1, +1, +1, +1], I = [-1, 0, -1, -1]
     * Pos 0: mismatch    CNT=0
     * Pos 1: zero, skip  Z=1
     * Pos 2: mismatch    CNT=0
     * Pos 3: mismatch    CNT=0
     * P = 2*0 - (4-1) = -3
     * True: -1 + 0 + -1 + -1 = -3 ✓ */
    ss_weight_t w[] = {1, 1, 1, 1};
    ss_input_t  x[] = {-1, 0, -1, -1};

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 4);
    ASSERT_EQ(r.dot_product, -3, "Should be -3");
    ASSERT_EQ(r.z_count, 1, "One zero");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 8. Auto-Mode Dispatch Tests                                           */
/* ===================================================================== */

static void test_dot_auto_bnn_mode(void)
{
    TEST(dot_auto_dispatches_bnn);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_BNN);

    ss_weight_t w[] = {1, -1};
    ss_input_t  x[] = {1, -1};
    /* Both match: CNT=2, P=2*2-2=2 */

    ss_dot_result_t r = ss_dot_auto(&hal, w, x, 2);
    ASSERT_EQ(r.dot_product, 2, "Auto BNN: dot should be 2");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_dot_auto_tbn_mode(void)
{
    TEST(dot_auto_dispatches_tbn);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_TBN);

    ss_weight_t w[] = {1, -1, 1};
    ss_input_t  x[] = {1, 0, -1};
    /* Pos 0: match CNT=1, Pos 1: zero Z=1, Pos 2: mismatch
     * P = 2*1 - (3-1) = 0
     * True: 1 + 0 - 1 = 0 ✓ */

    ss_dot_result_t r = ss_dot_auto(&hal, w, x, 3);
    ASSERT_EQ(r.dot_product, 0, "Auto TBN: dot should be 0");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 9. Matrix-Vector Multiplication Tests                                 */
/* ===================================================================== */

static void test_matmul_identity_like(void)
{
    TEST(matmul_diagonal_weights);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_BNN);

    /* 2×2 weight matrix, diagonal +1:
     * W = [+1, -1]    x = [+1]    y[0] = 1*1 + (-1)*(-1) = 2
     *     [-1, +1]        [-1]    y[1] = (-1)*1 + 1*(-1) = -2
     */
    ss_weight_t W[] = {1, -1,
                       -1,  1};
    ss_input_t  x[] = {1, -1};
    int y[2];

    int rc = ss_matmul(&hal, W, x, 2, 2, y);
    ASSERT_EQ(rc, 0, "matmul should succeed");
    ASSERT_EQ(y[0], 2, "y[0] should be 2");
    ASSERT_EQ(y[1], -2, "y[1] should be -2");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_matmul_3x4_tbn(void)
{
    TEST(matmul_3x4_tbn_with_zeros);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_TBN);

    /* 3×4 weight matrix:
     * W = [+1, +1, -1, -1]   x = [+1, 0, -1, +1]
     *     [-1, -1, +1, +1]
     *     [+1, -1, +1, -1]
     *
     * y[0] = 1*1 + 1*0 + (-1)(-1) + (-1)(1) = 1+0+1-1 = 1
     * y[1] = (-1)(1) + (-1)(0) + 1(-1) + 1(1) = -1+0-1+1 = -1
     * y[2] = 1(1) + (-1)(0) + 1(-1) + (-1)(1) = 1+0-1-1 = -1
     */
    ss_weight_t W[] = { 1,  1, -1, -1,
                        -1, -1,  1,  1,
                         1, -1,  1, -1};
    ss_input_t  x[] = {1, 0, -1, 1};
    int y[3];

    int rc = ss_matmul(&hal, W, x, 3, 4, y);
    ASSERT_EQ(rc, 0, "matmul should succeed");
    ASSERT_EQ(y[0], 1, "y[0] should be 1");
    ASSERT_EQ(y[1], -1, "y[1] should be -1");
    ASSERT_EQ(y[2], -1, "y[2] should be -1");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_matmul_1x1(void)
{
    TEST(matmul_1x1_trivial);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    ss_weight_t W[] = {-1};
    ss_input_t  x[] = {1};
    int y[1];

    int rc = ss_matmul(&hal, W, x, 1, 1, y);
    ASSERT_EQ(rc, 0, "matmul 1x1 should succeed");
    ASSERT_EQ(y[0], -1, "(-1)*(1) = -1");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_matmul_null_guard(void)
{
    TEST(matmul_null_inputs_fail);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    int rc = ss_matmul(&hal, NULL, NULL, 1, 1, NULL);
    ASSERT_EQ(rc, -1, "NULL inputs should return -1");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 10. Activation Function Tests                                         */
/* ===================================================================== */

static void test_activation_sign(void)
{
    TEST(activation_sign_function);

    ASSERT_EQ(ss_activation_sign(5), SS_INPUT_POS, "positive → +1");
    ASSERT_EQ(ss_activation_sign(-3), SS_INPUT_NEG, "negative → -1");
    ASSERT_EQ(ss_activation_sign(0), SS_INPUT_POS, "zero → +1 (convention)");

    PASS();
}

static void test_activation_ternary(void)
{
    TEST(activation_ternary_with_threshold);

    int t = 2;  /* threshold */
    ASSERT_EQ(ss_activation_ternary(5, t), SS_INPUT_POS, "5>2 → +1");
    ASSERT_EQ(ss_activation_ternary(-5, t), SS_INPUT_NEG, "-5<-2 → -1");
    ASSERT_EQ(ss_activation_ternary(1, t), SS_INPUT_ZERO, "|1|<=2 → 0");
    ASSERT_EQ(ss_activation_ternary(0, t), SS_INPUT_ZERO, "|0|<=2 → 0");
    ASSERT_EQ(ss_activation_ternary(-2, t), SS_INPUT_ZERO, "|-2|<=2 → 0");

    PASS();
}

/* ===================================================================== */
/* 11. Multi-Layer DNN Inference Tests                                   */
/* ===================================================================== */

static void test_dnn_two_layers(void)
{
    TEST(dnn_inference_two_layers);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_TBN);

    /* Layer 0: 2×3 (2 outputs from 3 inputs)
     * W0 = [+1, +1, -1]   Input = [+1, -1, +1]
     *      [-1, +1, +1]
     *
     * y0[0] = 1-1-1 = -1  → sign → -1
     * y0[1] = -1-1+1 = -1 → sign → -1
     *
     * Layer 1: 1×2 (1 output from 2 inputs)
     * W1 = [+1, -1]  Activated input = [-1, -1]
     *
     * y1[0] = (+1)(-1) + (-1)(-1) = -1+1 = 0
     */
    ss_weight_t W0[] = { 1,  1, -1,
                         -1,  1,  1};
    ss_weight_t W1[] = { 1, -1};

    ss_layer_config_t layers[2];
    layers[0].weights  = W0;
    layers[0].rows     = 2;
    layers[0].cols     = 3;
    layers[0].plane_id = -1;
    layers[0].block_id = -1;

    layers[1].weights  = W1;
    layers[1].rows     = 1;
    layers[1].cols     = 2;
    layers[1].plane_id = -1;
    layers[1].block_id = -1;

    ss_dnn_config_t config;
    config.layers     = layers;
    config.num_layers = 2;
    config.par_level  = SS_PAR_SEQUENTIAL;

    ss_input_t input[] = {1, -1, 1};
    int output[1];

    int rc = ss_dnn_inference(&hal, &config, input, 3, output, 1, 0);
    ASSERT_EQ(rc, 0, "DNN inference should succeed");
    ASSERT_EQ(output[0], 0, "Final output should be 0");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 12. HAL Lifecycle Tests                                               */
/* ===================================================================== */

static void test_hal_init_shutdown(void)
{
    TEST(hal_init_and_shutdown);

    ss_hal_state_t hal;
    int rc = ss_hal_init(&hal);
    ASSERT_EQ(rc, 0, "init should succeed");
    ASSERT_TRUE(ss_hal_ready(&hal), "HAL should be ready after init");
    ASSERT_EQ(hal.mode, SS_MODE_EMULATED, "Should be in emulation mode");

    rc = ss_hal_shutdown(&hal);
    ASSERT_EQ(rc, 0, "shutdown should succeed");
    ASSERT_TRUE(!ss_hal_ready(&hal), "HAL should not be ready after shutdown");

    PASS();
}

static void test_hal_null_guard(void)
{
    TEST(hal_null_state_guard);

    ASSERT_EQ(ss_hal_init(NULL), -1, "init(NULL) should return -1");
    ASSERT_EQ(ss_hal_shutdown(NULL), -1, "shutdown(NULL) should return -1");
    ASSERT_EQ(ss_hal_mode(NULL), SS_MODE_EMULATED, "mode(NULL) → emulated");
    ASSERT_TRUE(!ss_hal_ready(NULL), "ready(NULL) should be false");

    PASS();
}

static void test_hal_default_caps(void)
{
    TEST(hal_emulated_capabilities);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    ASSERT_EQ(hal.caps.chip_id, SS_CHIP_ID_EXPECTED, "chip ID should match");
    ASSERT_TRUE(hal.caps.has_bnn, "Should support BNN");
    ASSERT_TRUE(hal.caps.has_tbn, "Should support TBN");
    ASSERT_TRUE(hal.caps.has_zid, "Should support ZID");
    ASSERT_TRUE(hal.caps.num_planes >= 2, "Should have >= 2 planes");
    ASSERT_TRUE(hal.caps.sa_bits >= 1, "SA bits should be >= 1");
    ASSERT_TRUE(hal.caps.counter_bits >= 16, "Counter should be >= 16 bits");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 13. Mode Configuration Tests                                          */
/* ===================================================================== */

static void test_set_mode_bnn(void)
{
    TEST(set_mode_to_bnn);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    int rc = ss_hal_set_mode(&hal, SS_MODE_BNN);
    ASSERT_EQ(rc, 0, "set_mode BNN should succeed");
    ASSERT_EQ(hal.net_mode, SS_MODE_BNN, "Mode should be BNN");
    ASSERT_EQ(hal.zid_enabled, 0, "ZID should be off in BNN");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_set_mode_tbn(void)
{
    TEST(set_mode_to_tbn);

    ss_hal_state_t hal;
    ss_hal_init(&hal);
    ss_hal_set_mode(&hal, SS_MODE_BNN);  /* First switch to BNN */

    int rc = ss_hal_set_mode(&hal, SS_MODE_TBN);
    ASSERT_EQ(rc, 0, "set_mode TBN should succeed");
    ASSERT_EQ(hal.net_mode, SS_MODE_TBN, "Mode should be TBN");
    ASSERT_EQ(hal.zid_enabled, 1, "ZID should be on in TBN");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_set_mode_uninitialized(void)
{
    TEST(set_mode_on_uninit_fails);

    ss_hal_state_t hal;
    memset(&hal, 0, sizeof(hal));  /* Not initialized */
    ASSERT_EQ(ss_hal_set_mode(&hal, SS_MODE_TBN), -1,
              "set_mode on uninit HAL should fail");

    PASS();
}

/* ===================================================================== */
/* 14. Parallelism Configuration Tests                                   */
/* ===================================================================== */

static void test_set_parallelism_sequential(void)
{
    TEST(parallelism_sequential);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    int rc = ss_hal_set_parallelism(&hal, SS_PAR_SEQUENTIAL);
    ASSERT_EQ(rc, 0, "Sequential should always succeed");
    ASSERT_EQ(hal.par_level, SS_PAR_SEQUENTIAL, "Level should be sequential");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_set_parallelism_multi_block(void)
{
    TEST(parallelism_multi_block);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    int rc = ss_hal_set_parallelism(&hal, SS_PAR_MULTI_BLOCK);
    ASSERT_EQ(rc, 0, "Multi-block should succeed (caps have >=4 blocks)");
    ASSERT_EQ(hal.par_level, SS_PAR_MULTI_BLOCK, "Level should be multi-block");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_set_parallelism_pipelined(void)
{
    TEST(parallelism_pipelined);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    int rc = ss_hal_set_parallelism(&hal, SS_PAR_PIPELINED);
    ASSERT_EQ(rc, 0, "Pipelining should succeed (caps support it)");
    ASSERT_EQ(hal.par_level, SS_PAR_PIPELINED, "Level should be pipelined");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 15. Weight Programming Tests                                          */
/* ===================================================================== */

static void test_program_weights_emulated(void)
{
    TEST(program_weights_emulated_noop);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    ss_weight_t W[] = {1, -1, 1, -1};
    int rc = ss_program_weights(&hal, W, 2, 2, 0);
    ASSERT_EQ(rc, 0, "program_weights should succeed in emulation");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_read_weights_emulated(void)
{
    TEST(read_weights_emulated);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    ss_weight_t W[4];
    int rc = ss_read_weights(&hal, W, 2, 2, 0);
    ASSERT_EQ(rc, 0, "read_weights should succeed");
    /* Emulated returns all +1 */
    ASSERT_EQ(W[0], SS_WEIGHT_POS, "Emulated read should return +1");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_program_weights_null_guard(void)
{
    TEST(program_weights_null_guard);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    ASSERT_EQ(ss_program_weights(&hal, NULL, 2, 2, 0), -1,
              "NULL weights should return -1");
    ASSERT_EQ(ss_program_weights(&hal, (ss_weight_t[]){1}, 0, 1, 0), -1,
              "Zero rows should return -1");
    ASSERT_EQ(ss_program_weights(&hal, (ss_weight_t[]){1}, 1, 1, -1), -1,
              "Negative block_id should return -1");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 16. Patent-Specific Verification                                      */
/* ===================================================================== */

static void test_patent_eq1_formula(void)
{
    TEST(patent_eq1_bnn_formula_verification);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* Verify Eq. 1: P = 2*CNT - S
     * 8-element vector: W = all +1, I = [+1,-1,+1,-1,+1,-1,+1,-1]
     * Matches at 0,2,4,6: CNT=4, S=8
     * P = 2*4 - 8 = 0
     * True: sum of w[i]*x[i] = 1-1+1-1+1-1+1-1 = 0 ✓ */
    ss_weight_t w[8] = {1,1,1,1,1,1,1,1};
    ss_input_t  x[8] = {1,-1,1,-1,1,-1,1,-1};

    ss_dot_result_t r = ss_dot_bnn(&hal, w, x, 8);
    ASSERT_EQ(r.cnt_out, 4, "CNT should be 4");
    ASSERT_EQ(r.s_total, 8, "S should be 8");
    ASSERT_EQ(r.dot_product, 2*4 - 8, "P = 2*CNT - S = 0");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_patent_eq2_formula(void)
{
    TEST(patent_eq2_tbn_formula_verification);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* Verify Eq. 2: P = 2*CNT - (S-Z)
     * 6 elements: W = [+1,-1,+1,-1,+1,-1]
     *             I = [+1, 0,-1, 0,+1, 0]
     *
     * Pos 0: match (1,1)  CNT=1
     * Pos 1: zero         Z=1
     * Pos 2: mismatch     CNT=1
     * Pos 3: zero         Z=2
     * Pos 4: match (1,1)  CNT=2
     * Pos 5: zero         Z=3
     *
     * CNT=2, S=6, Z=3, S_eff=3
     * P = 2*2 - 3 = 1
     * True: 1+0-1+0+1+0 = 1 ✓ */
    ss_weight_t w[6] = {1,-1,1,-1,1,-1};
    ss_input_t  x[6] = {1, 0,-1, 0,1, 0};

    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 6);
    ASSERT_EQ(r.cnt_out, 2, "CNT should be 2");
    ASSERT_EQ(r.z_count, 3, "Z should be 3");
    ASSERT_EQ(r.s_effective, 3, "S_eff = S-Z = 3");
    ASSERT_EQ(r.dot_product, 2*2 - 3, "P = 2*CNT - (S-Z) = 1");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_xnor_property(void)
{
    TEST(synapse_implements_xnor);

    /* The patent states: unit synapse output = XNOR(input, weight)
     * for binary inputs.  Verify all 4 cases. */
    ss_weight_t ws[] = {1, 1, -1, -1};
    ss_input_t  is[] = {1, -1, 1, -1};
    int expect[]     = {1,  0, 0,  1};  /* XNOR truth table */

    for (int i = 0; i < 4; i++) {
        ss_unit_synapse_t s = ss_synapse_program(ws[i]);
        ss_voltage_pattern_t vp = ss_encode_input(is[i]);
        int conducts = ss_synapse_eval(s, vp);

        if (conducts != expect[i]) {
            FAIL("XNOR property violated");
            return;
        }
    }

    PASS();
}

/* ===================================================================== */
/* 17. Edge Cases and Larger Vectors                                     */
/* ===================================================================== */

static void test_large_vector_dot(void)
{
    TEST(dot_product_64_element_vector);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* 64 elements: alternating weights, first 32 inputs +1, next 32 -1 */
    ss_weight_t w[64];
    ss_input_t  x[64];

    for (int i = 0; i < 64; i++) {
        w[i] = (i % 2 == 0) ? 1 : -1;
    }
    for (int i = 0; i < 32; i++) x[i] = 1;
    for (int i = 32; i < 64; i++) x[i] = -1;

    /* Manual calculation:
     * For i in [0,31]: x[i]=+1
     *   Even i (0,2,...,30): w=+1 → match (16 matches)
     *   Odd i  (1,3,...,31): w=-1 → mismatch
     * For i in [32,63]: x[i]=-1
     *   Even i (32,34,...,62): w=+1 → mismatch
     *   Odd i  (33,35,...,63): w=-1 → match (16 matches)
     * Total CNT = 32, S = 64
     * P = 2*32 - 64 = 0
     *
     * Verification: sum of w[i]*x[i]:
     *   First 32: 16*(+1)*(+1) + 16*(-1)*(+1) = 16 - 16 = 0
     *   Next 32:  16*(+1)*(-1) + 16*(-1)*(-1) = -16 + 16 = 0
     *   Total: 0 ✓ */
    ss_dot_result_t r = ss_dot_bnn(&hal, w, x, 64);
    ASSERT_EQ(r.dot_product, 0, "64-element alternating: dot should be 0");
    ASSERT_EQ(r.cnt_out, 32, "Should have 32 matches");

    ss_hal_shutdown(&hal);
    PASS();
}

static void test_tbn_large_sparse(void)
{
    TEST(tbn_large_sparse_vector);

    ss_hal_state_t hal;
    ss_hal_init(&hal);

    /* 16 elements, mostly zero (sparse) */
    ss_weight_t w[16];
    ss_input_t  x[16];
    memset(x, 0, sizeof(x));  /* All zeros */
    for (int i = 0; i < 16; i++) w[i] = (i % 2 == 0) ? 1 : -1;

    /* Set only positions 0 and 15 as non-zero */
    x[0]  = 1;   /* W=+1, match */
    x[15] = -1;  /* W=-1, match */

    /* Z=14, CNT=2, S=16, S_eff=2
     * P = 2*2 - 2 = 2
     * True: 1*1 + 0*13_terms + (-1)*(-1) = 1+1 = 2 ✓ */
    ss_dot_result_t r = ss_dot_tbn(&hal, w, x, 16);
    ASSERT_EQ(r.dot_product, 2, "Sparse dot should be 2");
    ASSERT_EQ(r.z_count, 14, "14 zeros");
    ASSERT_EQ(r.cnt_out, 2, "2 matches");

    ss_hal_shutdown(&hal);
    PASS();
}

/* ===================================================================== */
/* 18. MMIO Register Constant Validation                                 */
/* ===================================================================== */

static void test_mmio_constants(void)
{
    TEST(mmio_register_offsets_valid);

    /* Verify non-overlapping register regions */
    ASSERT_TRUE(SS_REG_CHIP_ID < SS_REG_MODE, "ID < MODE region");
    ASSERT_TRUE(SS_REG_MODE < SS_REG_INPUT_VEC_BASE, "MODE < INPUT region");
    ASSERT_TRUE(SS_REG_INPUT_VEC_BASE < SS_REG_WEIGHT_PROG, "INPUT < WEIGHT");
    ASSERT_TRUE(SS_REG_WEIGHT_PROG < SS_REG_CNT_OUT, "WEIGHT < COUNTER");
    ASSERT_TRUE(SS_REG_CNT_OUT < SS_REG_BLOCK_SELECT, "COUNTER < BLOCK");
    ASSERT_TRUE(SS_REG_BLOCK_SELECT < SS_REG_ZID_CTRL, "BLOCK < ZID");
    ASSERT_TRUE(SS_REG_ZID_CTRL < SS_REG_COMMAND, "ZID < COMMAND");

    /* Verify feature flags are distinct */
    ASSERT_EQ(SS_FEAT_BNN & SS_FEAT_TBN, 0u, "BNN and TBN flags distinct");
    ASSERT_EQ(SS_FEAT_ZID & SS_FEAT_MULTI_BLOCK, 0u, "ZID and MBLK distinct");

    PASS();
}

static void test_topology_packing(void)
{
    TEST(topology_register_pack_unpack);

    uint32_t topo = SS_TOPO_PACK(2, 4, 64, 128);
    ASSERT_EQ(SS_TOPO_PLANES(topo), 2u, "Planes should be 2");
    ASSERT_EQ(SS_TOPO_BLOCKS(topo), 4u, "Blocks should be 4");
    ASSERT_EQ(SS_TOPO_STRINGS(topo), 64u, "Strings should be 64");
    ASSERT_EQ(SS_TOPO_SYNAPSES(topo), 128u, "Synapses should be 128");

    PASS();
}

/* ===================================================================== */
/* Main                                                                  */
/* ===================================================================== */

int main(void)
{
    printf("=== Samsung US11170290B2 NAND Inference HAL Test Suite ===\n\n");

    printf("[1] Weight Encoding\n");
    test_weight_valid();
    test_synapse_program_pos();
    test_synapse_program_neg();
    test_synapse_read_weight();

    printf("\n[2] Voltage Pattern Encoding\n");
    test_encode_input_neg();
    test_encode_input_pos();
    test_encode_input_zero();
    test_is_zero_input();

    printf("\n[3] Cell Conductivity\n");
    test_cell_conducts_erased_vread();
    test_cell_programmed_vread();
    test_cell_any_vpass();

    printf("\n[4] Unit Synapse Evaluation (Patent Cases 1-6)\n");
    test_synapse_case1();
    test_synapse_case2();
    test_synapse_case3();
    test_synapse_case4();
    test_synapse_case5();
    test_synapse_case6();

    printf("\n[5] Zero Input Detection (ZID)\n");
    test_zid_count_no_zeros();
    test_zid_count_some_zeros();
    test_zid_count_all_zeros();
    test_zid_bitmap_pattern();
    test_zid_bitmap_empty();

    printf("\n[6] BNN Dot-Product (Eq. 1)\n");
    test_bnn_dot_all_match();
    test_bnn_dot_all_mismatch();
    test_bnn_dot_mixed();
    test_bnn_dot_single();

    printf("\n[7] TBN Dot-Product (Eq. 2)\n");
    test_tbn_dot_no_zeros();
    test_tbn_dot_with_zeros();
    test_tbn_dot_all_zeros();
    test_tbn_dot_single_zero();
    test_tbn_dot_asymmetric();
    test_tbn_dot_negative_result();

    printf("\n[8] Auto-Mode Dispatch\n");
    test_dot_auto_bnn_mode();
    test_dot_auto_tbn_mode();

    printf("\n[9] Matrix-Vector Multiplication\n");
    test_matmul_identity_like();
    test_matmul_3x4_tbn();
    test_matmul_1x1();
    test_matmul_null_guard();

    printf("\n[10] Activation Functions\n");
    test_activation_sign();
    test_activation_ternary();

    printf("\n[11] Multi-Layer DNN Inference\n");
    test_dnn_two_layers();

    printf("\n[12] HAL Lifecycle\n");
    test_hal_init_shutdown();
    test_hal_null_guard();
    test_hal_default_caps();

    printf("\n[13] Mode Configuration\n");
    test_set_mode_bnn();
    test_set_mode_tbn();
    test_set_mode_uninitialized();

    printf("\n[14] Parallelism Configuration\n");
    test_set_parallelism_sequential();
    test_set_parallelism_multi_block();
    test_set_parallelism_pipelined();

    printf("\n[15] Weight Programming\n");
    test_program_weights_emulated();
    test_read_weights_emulated();
    test_program_weights_null_guard();

    printf("\n[16] Patent Formula Verification\n");
    test_patent_eq1_formula();
    test_patent_eq2_formula();
    test_xnor_property();

    printf("\n[17] Edge Cases / Large Vectors\n");
    test_large_vector_dot();
    test_tbn_large_sparse();

    printf("\n[18] MMIO Constants\n");
    test_mmio_constants();
    test_topology_packing();

    printf("\n=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);

    return tests_failed ? EXIT_FAILURE : EXIT_SUCCESS;
}
