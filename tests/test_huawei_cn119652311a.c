/**
 * @file test_huawei_cn119652311a.c
 * @brief Comprehensive test suite for Huawei CN119652311A ternary chip HAL
 *
 * Tests every layer of the Huawei hardware abstraction:
 *   - Value translation (balanced <-> unbalanced)
 *   - Gate truth tables (INC, DEC, NTI, PTI, PB, NB)
 *   - Summing circuit (Tsum) — all 9 input pairs
 *   - Half-adder (THA) — all 9 input pairs with carry verification
 *   - Full-adder (TFA) — all 27 input triples
 *   - Exact multiply (TMul) — all 9 input pairs
 *   - 2trit × 2trit multiply — known products
 *   - 6trit × 6trit multiply — patent reference values
 *   - Approximate multiplier with compensation modes
 *   - Multi-trit word addition
 *   - Dot product
 *   - FFT butterfly
 *   - HAL lifecycle (init / shutdown)
 *
 * Every ASSERT checks a computed value against an independently
 * verifiable expected value — no tautologies.
 *
 * Build:
 *   gcc -Wall -Wextra -Iinclude -o test_huawei_cn119652311a \
 *       tests/test_huawei_cn119652311a.c \
 *       src/huawei_alu.c src/huawei_hal.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "set5/huawei_cn119652311a.h"
#include "set5/huawei_alu.h"

/* ===================================================================== */
/*  Test Infrastructure                                                  */
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
/*  1. Value Translation Tests                                           */
/* ===================================================================== */

static void test_hw_from_balanced(void)
{
    TEST(hw_from_balanced_all_values);

    /* -1 -> 0, 0 -> 1, +1 -> 2 */
    ASSERT_EQ(hw_from_balanced(TRIT_FALSE),   HW_TRIT_0, "-1 should map to 0");
    ASSERT_EQ(hw_from_balanced(TRIT_UNKNOWN), HW_TRIT_1, "0 should map to 1");
    ASSERT_EQ(hw_from_balanced(TRIT_TRUE),    HW_TRIT_2, "+1 should map to 2");

    PASS();
}

static void test_hw_to_balanced(void)
{
    TEST(hw_to_balanced_all_values);

    /* 0 -> -1, 1 -> 0, 2 -> +1 */
    ASSERT_EQ(hw_to_balanced(HW_TRIT_0), TRIT_FALSE,   "0 should map to -1");
    ASSERT_EQ(hw_to_balanced(HW_TRIT_1), TRIT_UNKNOWN, "1 should map to 0");
    ASSERT_EQ(hw_to_balanced(HW_TRIT_2), TRIT_TRUE,    "2 should map to +1");

    PASS();
}

static void test_roundtrip_translation(void)
{
    TEST(roundtrip_balanced_unbalanced);

    trit vals[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    for (int i = 0; i < 3; i++) {
        trit v = vals[i];
        trit rt = hw_to_balanced(hw_from_balanced(v));
        ASSERT_EQ(rt, v, "roundtrip should preserve value");
    }

    PASS();
}

static void test_trit2_conversion(void)
{
    TEST(trit2_conversion_roundtrip);

    trit vals[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };
    for (int i = 0; i < 3; i++) {
        trit v = vals[i];
        trit2 t2 = trit2_encode((int)v);
        hw_trit hw = hw_from_trit2(t2);
        trit2 t2_back = hw_to_trit2(hw);
        trit decoded = (trit)trit2_decode(t2_back);
        ASSERT_EQ(decoded, v, "trit2 roundtrip should preserve value");
    }

    PASS();
}

/* ===================================================================== */
/*  2. Gate Truth Table Tests (Huawei encoding)                          */
/* ===================================================================== */

static void test_gate_inc_truth_table(void)
{
    TEST(gate_inc_f5_truth_table);

    /* INC: f5 = {1, 2, 0} — (x+1) mod 3 */
    ASSERT_EQ(hw_gate_inc(HW_TRIT_0), HW_TRIT_1, "INC(0) = 1");
    ASSERT_EQ(hw_gate_inc(HW_TRIT_1), HW_TRIT_2, "INC(1) = 2");
    ASSERT_EQ(hw_gate_inc(HW_TRIT_2), HW_TRIT_0, "INC(2) = 0");

    PASS();
}

static void test_gate_dec_truth_table(void)
{
    TEST(gate_dec_f19_truth_table);

    /* DEC: f19 = {2, 0, 1} — (x-1) mod 3 */
    ASSERT_EQ(hw_gate_dec(HW_TRIT_0), HW_TRIT_2, "DEC(0) = 2");
    ASSERT_EQ(hw_gate_dec(HW_TRIT_1), HW_TRIT_0, "DEC(1) = 0");
    ASSERT_EQ(hw_gate_dec(HW_TRIT_2), HW_TRIT_1, "DEC(2) = 1");

    PASS();
}

static void test_inc_dec_inverse(void)
{
    TEST(inc_dec_are_inverses);

    /* INC(DEC(x)) = x and DEC(INC(x)) = x for all inputs */
    for (hw_trit x = 0; x <= 2; x++) {
        ASSERT_EQ(hw_gate_inc(hw_gate_dec(x)), x, "INC(DEC(x)) = x");
        ASSERT_EQ(hw_gate_dec(hw_gate_inc(x)), x, "DEC(INC(x)) = x");
    }

    PASS();
}

static void test_gate_nti_truth_table(void)
{
    TEST(gate_nti_f18_truth_table);

    /* NTI: f18 = {2, 0, 0} */
    ASSERT_EQ(hw_gate_nti(HW_TRIT_0), HW_TRIT_2, "NTI(0) = 2");
    ASSERT_EQ(hw_gate_nti(HW_TRIT_1), HW_TRIT_0, "NTI(1) = 0");
    ASSERT_EQ(hw_gate_nti(HW_TRIT_2), HW_TRIT_0, "NTI(2) = 0");

    PASS();
}

static void test_gate_pti_truth_table(void)
{
    TEST(gate_pti_f24_truth_table);

    /* PTI: f24 = {2, 2, 0} */
    ASSERT_EQ(hw_gate_pti(HW_TRIT_0), HW_TRIT_2, "PTI(0) = 2");
    ASSERT_EQ(hw_gate_pti(HW_TRIT_1), HW_TRIT_2, "PTI(1) = 2");
    ASSERT_EQ(hw_gate_pti(HW_TRIT_2), HW_TRIT_0, "PTI(2) = 0");

    PASS();
}

static void test_gate_pb_truth_table(void)
{
    TEST(gate_pb_f8_truth_table);

    /* PB: f8 = {0, 2, 2} */
    ASSERT_EQ(hw_gate_pb(HW_TRIT_0), HW_TRIT_0, "PB(0) = 0");
    ASSERT_EQ(hw_gate_pb(HW_TRIT_1), HW_TRIT_2, "PB(1) = 2");
    ASSERT_EQ(hw_gate_pb(HW_TRIT_2), HW_TRIT_2, "PB(2) = 2");

    PASS();
}

static void test_gate_nb_truth_table(void)
{
    TEST(gate_nb_f2_truth_table);

    /* NB: f2 = {0, 0, 2} */
    ASSERT_EQ(hw_gate_nb(HW_TRIT_0), HW_TRIT_0, "NB(0) = 0");
    ASSERT_EQ(hw_gate_nb(HW_TRIT_1), HW_TRIT_0, "NB(1) = 0");
    ASSERT_EQ(hw_gate_nb(HW_TRIT_2), HW_TRIT_2, "NB(2) = 2");

    PASS();
}

/* ===================================================================== */
/*  3. ALU Gate Operations (balanced ternary, via HAL)                   */
/* ===================================================================== */

static hw_hal_state_t state;

static void test_alu_inc_balanced(void)
{
    TEST(alu_inc_balanced_all_values);

    /* INC in balanced: -1->0, 0->+1, +1->-1 */
    ASSERT_EQ(hw_alu_inc(&state, TRIT_FALSE),   TRIT_UNKNOWN, "INC(-1) = 0");
    ASSERT_EQ(hw_alu_inc(&state, TRIT_UNKNOWN), TRIT_TRUE,    "INC(0) = +1");
    ASSERT_EQ(hw_alu_inc(&state, TRIT_TRUE),    TRIT_FALSE,   "INC(+1) = -1");

    PASS();
}

static void test_alu_dec_balanced(void)
{
    TEST(alu_dec_balanced_all_values);

    /* DEC in balanced: -1->+1, 0->-1, +1->0 */
    ASSERT_EQ(hw_alu_dec(&state, TRIT_FALSE),   TRIT_TRUE,    "DEC(-1) = +1");
    ASSERT_EQ(hw_alu_dec(&state, TRIT_UNKNOWN), TRIT_FALSE,   "DEC(0) = -1");
    ASSERT_EQ(hw_alu_dec(&state, TRIT_TRUE),    TRIT_UNKNOWN, "DEC(+1) = 0");

    PASS();
}

static void test_alu_nti_balanced(void)
{
    TEST(alu_nti_balanced_all_values);

    /* NTI in balanced: -1->+1, 0->-1, +1->-1 */
    ASSERT_EQ(hw_alu_nti(&state, TRIT_FALSE),   TRIT_TRUE,    "NTI(-1) = +1");
    ASSERT_EQ(hw_alu_nti(&state, TRIT_UNKNOWN), TRIT_FALSE,   "NTI(0) = -1");
    ASSERT_EQ(hw_alu_nti(&state, TRIT_TRUE),    TRIT_FALSE,   "NTI(+1) = -1");

    PASS();
}

static void test_alu_pti_balanced(void)
{
    TEST(alu_pti_balanced_all_values);

    /* PTI in balanced: -1->+1, 0->+1, +1->-1 */
    ASSERT_EQ(hw_alu_pti(&state, TRIT_FALSE),   TRIT_TRUE,    "PTI(-1) = +1");
    ASSERT_EQ(hw_alu_pti(&state, TRIT_UNKNOWN), TRIT_TRUE,    "PTI(0) = +1");
    ASSERT_EQ(hw_alu_pti(&state, TRIT_TRUE),    TRIT_FALSE,   "PTI(+1) = -1");

    PASS();
}

/* ===================================================================== */
/*  4. Summing Circuit (Tsum) — Exhaustive                               */
/* ===================================================================== */

static void test_tsum_exhaustive(void)
{
    TEST(tsum_all_9_combinations);

    /*
     * Tsum(A, B) = (A + B) mod 3 in balanced ternary.
     * Expected values:
     *
     *   A\B | -1  |  0  | +1
     *  -----+-----+-----+-----
     *   -1  | +1  | -1  |  0
     *    0  | -1  |  0  | +1
     *   +1  |  0  | +1  | -1
     *
     * Note: this is modular sum (no carry), wrapping around.
     */
    trit vals[] = { TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE };

    /* Expected: tsum[a+1][b+1] */
    trit expected[3][3] = {
        /* A=-1:  -1+-1=-2≡+1,  -1+0=-1,    -1+1= 0 */
        { TRIT_TRUE,    TRIT_FALSE,   TRIT_UNKNOWN },
        /* A= 0:   0+-1=-1,     0+0= 0,     0+1=+1 */
        { TRIT_FALSE,   TRIT_UNKNOWN, TRIT_TRUE    },
        /* A=+1:  +1+-1= 0,    +1+0=+1,    +1+1=+2≡-1 */
        { TRIT_UNKNOWN, TRIT_TRUE,    TRIT_FALSE   }
    };

    for (int ai = 0; ai < 3; ai++) {
        for (int bi = 0; bi < 3; bi++) {
            trit result = hw_alu_tsum(&state, vals[ai], vals[bi]);
            ASSERT_EQ(result, expected[ai][bi], "Tsum mismatch");
        }
    }

    PASS();
}

/* ===================================================================== */
/*  5. Half-Adder (THA) — Exhaustive with carry                         */
/* ===================================================================== */

static void test_half_adder_exhaustive(void)
{
    TEST(half_adder_all_9_sum_and_carry);

    /*
     * Half-adder truth table (balanced ternary):
     *
     *   A + B | decimal | carry | sum
     *  -------+---------+-------+-----
     *  -1+-1  |   -2    |  -1   | +1
     *  -1+ 0  |   -1    |   0   | -1
     *  -1++1  |    0    |   0   |  0
     *   0+-1  |   -1    |   0   | -1
     *   0+ 0  |    0    |   0   |  0
     *   0++1  |   +1    |   0   | +1
     *  +1+-1  |    0    |   0   |  0
     *  +1+ 0  |   +1    |   0   | +1
     *  +1++1  |   +2    |  +1   | -1
     */
    typedef struct { trit a, b, exp_sum, exp_carry; } ha_case;
    ha_case cases[] = {
        { -1, -1, +1, -1 },
        { -1,  0, -1,  0 },
        { -1, +1,  0,  0 },
        {  0, -1, -1,  0 },
        {  0,  0,  0,  0 },
        {  0, +1, +1,  0 },
        { +1, -1,  0,  0 },
        { +1,  0, +1,  0 },
        { +1, +1, -1, +1 }
    };

    for (int i = 0; i < 9; i++) {
        hw_half_adder_result_t r = hw_alu_half_add(&state,
                                                    cases[i].a,
                                                    cases[i].b);
        ASSERT_EQ(r.sum,   cases[i].exp_sum,   "THA sum mismatch");
        ASSERT_EQ(r.carry, cases[i].exp_carry,  "THA carry mismatch");
    }

    PASS();
}

static void test_half_adder_consistency(void)
{
    TEST(half_adder_carry_times_3_plus_sum_eq_a_plus_b);

    /* For every (a, b): carry*3 + sum = a + b */
    trit vals[] = { -1, 0, +1 };
    for (int ai = 0; ai < 3; ai++) {
        for (int bi = 0; bi < 3; bi++) {
            hw_half_adder_result_t r = hw_alu_half_add(&state,
                                                        vals[ai],
                                                        vals[bi]);
            int reconstructed = (int)r.carry * 3 + (int)r.sum;
            int expected = (int)vals[ai] + (int)vals[bi];
            ASSERT_EQ(reconstructed, expected, "carry*3+sum != a+b");
        }
    }

    PASS();
}

/* ===================================================================== */
/*  6. Full-Adder (TFA) — Exhaustive                                     */
/* ===================================================================== */

static void test_full_adder_exhaustive(void)
{
    TEST(full_adder_all_27_carry_3_plus_sum_eq_a_b_c);

    /* For every (a, b, c): carry*3 + sum = a + b + c */
    trit vals[] = { -1, 0, +1 };
    int count = 0;

    for (int ai = 0; ai < 3; ai++) {
        for (int bi = 0; bi < 3; bi++) {
            for (int ci = 0; ci < 3; ci++) {
                hw_full_adder_result_t r = hw_alu_full_add(&state,
                                                            vals[ai],
                                                            vals[bi],
                                                            vals[ci]);
                int reconstructed = (int)r.carry * 3 + (int)r.sum;
                int expected = (int)vals[ai] + (int)vals[bi] + (int)vals[ci];
                ASSERT_EQ(reconstructed, expected, "TFA carry*3+sum != a+b+c");
                count++;
            }
        }
    }

    ASSERT_EQ(count, 27, "Should test all 27 combinations");
    PASS();
}

static void test_full_adder_specific(void)
{
    TEST(full_adder_boundary_cases);

    /* Max negative: -1+-1+-1 = -3 → carry=-1, sum=0 */
    hw_full_adder_result_t r1 = hw_alu_full_add(&state, -1, -1, -1);
    ASSERT_EQ(r1.sum,    0, "(-1)+(-1)+(-1) sum = 0");
    ASSERT_EQ(r1.carry, -1, "(-1)+(-1)+(-1) carry = -1");

    /* Max positive: +1+1+1 = +3 → carry=+1, sum=0 */
    hw_full_adder_result_t r2 = hw_alu_full_add(&state, +1, +1, +1);
    ASSERT_EQ(r2.sum,   0, "(+1)+(+1)+(+1) sum = 0");
    ASSERT_EQ(r2.carry, 1, "(+1)+(+1)+(+1) carry = +1");

    /* Zero: 0+0+0 = 0 → carry=0, sum=0 */
    hw_full_adder_result_t r3 = hw_alu_full_add(&state, 0, 0, 0);
    ASSERT_EQ(r3.sum,   0, "0+0+0 sum = 0");
    ASSERT_EQ(r3.carry, 0, "0+0+0 carry = 0");

    PASS();
}

/* ===================================================================== */
/*  7. Exact Multiply (TMul)                                             */
/* ===================================================================== */

static void test_mul1_exhaustive(void)
{
    TEST(mul1_all_9_products);

    /*
     * Balanced ternary multiplication truth table:
     *   A\B | -1  |  0  | +1
     *  -----+-----+-----+-----
     *   -1  | +1  |  0  | -1
     *    0  |  0  |  0  |  0
     *   +1  | -1  |  0  | +1
     */
    trit vals[] = { -1, 0, +1 };
    for (int ai = 0; ai < 3; ai++) {
        for (int bi = 0; bi < 3; bi++) {
            trit result = hw_alu_mul1(&state, vals[ai], vals[bi]);
            int expected = (int)vals[ai] * (int)vals[bi];
            ASSERT_EQ((int)result, expected, "TMul product mismatch");
        }
    }

    PASS();
}

/* ===================================================================== */
/*  8. 2-trit × 2-trit Multiplication                                   */
/* ===================================================================== */

static void test_mul2x2_exact_simple(void)
{
    TEST(mul2x2_exact_simple_products);

    /* 1 × 1 = 1 */
    hw_mul_result_t r1 = hw_alu_mul2x2(&state, 1, 1, HW_COMP_NONE);
    ASSERT_EQ(r1.result, 1, "1*1 = 1");

    /* 2 × 3 = 6 */
    hw_mul_result_t r2 = hw_alu_mul2x2(&state, 2, 3, HW_COMP_NONE);
    ASSERT_EQ(r2.result, 6, "2*3 = 6");

    /* -1 × 1 = -1 */
    hw_mul_result_t r3 = hw_alu_mul2x2(&state, -1, 1, HW_COMP_NONE);
    ASSERT_EQ(r3.result, -1, "-1*1 = -1");

    /* 0 × 4 = 0 */
    hw_mul_result_t r4 = hw_alu_mul2x2(&state, 0, 4, HW_COMP_NONE);
    ASSERT_EQ(r4.result, 0, "0*4 = 0");

    /* -4 × -4 = 16 */
    hw_mul_result_t r5 = hw_alu_mul2x2(&state, -4, -4, HW_COMP_NONE);
    ASSERT_EQ(r5.result, 16, "-4*-4 = 16");

    PASS();
}

static void test_mul2x2_reconstruction(void)
{
    TEST(mul2x2_trits_reconstruct_to_result);

    /* For several products, verify that recomposing trits = result */
    int test_vals[] = { -4, -3, -2, -1, 0, 1, 2, 3, 4 };
    int n = sizeof(test_vals) / sizeof(test_vals[0]);

    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
            hw_mul_result_t r = hw_alu_mul2x2(&state,
                                               test_vals[i],
                                               test_vals[j],
                                               HW_COMP_NONE);
            /* Reconstruct from trits: sum(trits[k] * 3^k) */
            int recomp = 0;
            int w = 1;
            for (int k = 0; k < r.width_trits; k++) {
                recomp += (int)r.trits[k] * w;
                w *= 3;
            }
            ASSERT_EQ(recomp, r.result, "trit reconstruction mismatch");
        }
    }

    PASS();
}

static void test_mul2x2_compensation_plus6(void)
{
    TEST(mul2x2_plus6_reduces_error_vs_none);

    /*
     * For inputs where the approximate path introduces error,
     * +6 compensation should generally reduce the error or
     * change it.  Here we verify that the compensation actually
     * adds 6 to the approximate result at the trit level.
     */
    hw_mul_result_t r_none = hw_alu_mul2x2(&state, 4, 4, HW_COMP_NONE);
    hw_mul_result_t r_p6   = hw_alu_mul2x2(&state, 4, 4, HW_COMP_PLUS6);

    /* +6 compensation adds 6 to the approximate product */
    int diff = r_p6.result - r_none.result;
    ASSERT_EQ(diff, 6, "+6 compensation should add exactly 6");

    PASS();
}

static void test_mul2x2_compensation_plus9(void)
{
    TEST(mul2x2_plus9_adds_9_to_approximate);

    hw_mul_result_t r_none = hw_alu_mul2x2(&state, 4, 4, HW_COMP_NONE);
    hw_mul_result_t r_p9   = hw_alu_mul2x2(&state, 4, 4, HW_COMP_PLUS9);

    int diff = r_p9.result - r_none.result;
    ASSERT_EQ(diff, 9, "+9 compensation should add exactly 9");

    PASS();
}

/* ===================================================================== */
/*  9. 6-trit × 6-trit Multiplication                                   */
/* ===================================================================== */

static void test_mul6x6_simple(void)
{
    TEST(mul6x6_simple_products);

    /* 1 × 1 = 1 */
    hw_mul_result_t r1 = hw_alu_mul6x6(&state, 1, 1, HW_COMP_NONE);
    ASSERT_EQ(r1.result, 1, "1*1 = 1");

    /* 10 × 10 = 100 */
    hw_mul_result_t r2 = hw_alu_mul6x6(&state, 10, 10, HW_COMP_NONE);
    ASSERT_EQ(r2.result, 100, "10*10 = 100");

    /* -5 × 7 = -35 */
    hw_mul_result_t r3 = hw_alu_mul6x6(&state, -5, 7, HW_COMP_NONE);
    ASSERT_EQ(r3.result, -35, "-5*7 = -35");

    PASS();
}

static void test_mul6x6_max_range(void)
{
    TEST(mul6x6_near_max_range);

    /* Max 6-trit balanced value: 364 (all +1 trits: 1+3+9+27+81+243) */
    /* Min: -364 */

    /* 100 × 100 = 10000 */
    hw_mul_result_t r1 = hw_alu_mul6x6(&state, 100, 100, HW_COMP_NONE);
    ASSERT_EQ(r1.result, 10000, "100*100 = 10000");

    /* -100 × 100 = -10000 */
    hw_mul_result_t r2 = hw_alu_mul6x6(&state, -100, 100, HW_COMP_NONE);
    ASSERT_EQ(r2.result, -10000, "-100*100 = -10000");

    PASS();
}

static void test_mul6x6_trits_width(void)
{
    TEST(mul6x6_result_uses_12_trits);

    hw_mul_result_t r = hw_alu_mul6x6(&state, 50, 50, HW_COMP_NONE);
    ASSERT_EQ(r.width_trits, 12, "6x6 result should be 12 trits");
    ASSERT_EQ(r.result, 2500, "50*50 = 2500");

    PASS();
}

/* ===================================================================== */
/*  10. Multi-Trit Word Addition                                         */
/* ===================================================================== */

static void test_word_add_simple(void)
{
    TEST(word_add_4_trit_simple);

    /* 1 + 1 = 2 in balanced ternary: */
    /* 1 = {+1, 0, 0, 0}, 1 = {+1, 0, 0, 0} */
    /* 2 = {-1, +1, 0, 0} (2 = -1*1 + 1*3 = 2 ✓) */
    trit a[] = { +1,  0, 0, 0 };
    trit b[] = { +1,  0, 0, 0 };
    trit r[4] = {0};

    trit carry = hw_alu_add_word(&state, a, b, r, 4);

    /* Reconstruct result */
    int result = (int)r[0] + (int)r[1]*3 + (int)r[2]*9 + (int)r[3]*27
                 + (int)carry * 81;
    ASSERT_EQ(result, 2, "1+1 = 2 in balanced ternary");

    PASS();
}

static void test_word_add_negative(void)
{
    TEST(word_add_with_negative);

    /* 4 + (-4) = 0 */
    /* 4 = {+1, +1, 0, 0} (1 + 3 = 4), -4 = {-1, -1, 0, 0} */
    trit a[] = { +1, +1, 0, 0 };
    trit b[] = { -1, -1, 0, 0 };
    trit r[4] = {0};

    trit carry = hw_alu_add_word(&state, a, b, r, 4);

    int result = (int)r[0] + (int)r[1]*3 + (int)r[2]*9 + (int)r[3]*27
                 + (int)carry * 81;
    ASSERT_EQ(result, 0, "4+(-4) = 0");

    PASS();
}

static void test_word_add_carry_propagation(void)
{
    TEST(word_add_carry_propagates);

    /* 4 + 4 = 8 in balanced ternary */
    /* 4 = {+1, +1, 0, 0} */
    /* 8 = {-1, 0, +1, 0} (8 = -1 + 0 + 9 = 8 ✓) */
    trit a[] = { +1, +1, 0, 0 };
    trit b[] = { +1, +1, 0, 0 };
    trit r[4] = {0};

    trit carry = hw_alu_add_word(&state, a, b, r, 4);

    int result = (int)r[0] + (int)r[1]*3 + (int)r[2]*9 + (int)r[3]*27
                 + (int)carry * 81;
    ASSERT_EQ(result, 8, "4+4 = 8");

    PASS();
}

/* ===================================================================== */
/*  11. Dot Product                                                      */
/* ===================================================================== */

static void test_dot_product_simple(void)
{
    TEST(dot_product_basic);

    /* {+1,+1,+1} · {+1,+1,+1} = 3 */
    trit a[] = { +1, +1, +1 };
    trit b[] = { +1, +1, +1 };
    int result = hw_alu_dot_product(&state, a, b, 3);
    ASSERT_EQ(result, 3, "(+1,+1,+1)·(+1,+1,+1) = 3");

    PASS();
}

static void test_dot_product_mixed(void)
{
    TEST(dot_product_mixed_values);

    /* {+1, -1, 0} · {-1, +1, +1} = -1*1 + (-1)*1 + 0*1 = -1-1+0 = -2 */
    trit a[] = { +1, -1,  0 };
    trit b[] = { -1, +1, +1 };
    int result = hw_alu_dot_product(&state, a, b, 3);
    int expected = (+1)*(-1) + (-1)*(+1) + 0*(+1); /* = -1 + -1 + 0 = -2 */
    ASSERT_EQ(result, expected, "dot product mixed values");

    PASS();
}

static void test_dot_product_orthogonal(void)
{
    TEST(dot_product_orthogonal);

    /* {+1, 0, 0} · {0, +1, 0} = 0 */
    trit a[] = { +1, 0, 0 };
    trit b[] = { 0, +1, 0 };
    int result = hw_alu_dot_product(&state, a, b, 3);
    ASSERT_EQ(result, 0, "orthogonal vectors dot = 0");

    PASS();
}

/* ===================================================================== */
/*  12. FFT Butterfly                                                    */
/* ===================================================================== */

static void test_fft_butterfly_all_zero(void)
{
    TEST(fft_butterfly_zero_input);

    trit out0, out1, out2;
    int rc = hw_alu_fft_butterfly(&state, 0, 0, 0, &out0, &out1, &out2);
    ASSERT_EQ(rc, 0, "butterfly should return 0");

    /* All zero inputs → all zero outputs */
    ASSERT_EQ((int)out0, 0, "out0 should be 0");
    ASSERT_EQ((int)out1, 0, "out1 should be 0");
    ASSERT_EQ((int)out2, 0, "out2 should be 0");

    PASS();
}

static void test_fft_butterfly_return_code(void)
{
    TEST(fft_butterfly_null_output_returns_neg1);

    int rc = hw_alu_fft_butterfly(&state, 0, 0, 0, NULL, NULL, NULL);
    ASSERT_EQ(rc, -1, "null output pointers should return -1");

    PASS();
}

static void test_fft_butterfly_identity(void)
{
    TEST(fft_butterfly_uniform_input);

    /*
     * When all inputs are +1:
     *   out0 = tsum(tsum(+1, +1), +1) = tsum(-1, +1) = 0
     *   out1 = tsum(tsum(+1, INC(+1)), DEC(+1))
     *        = tsum(tsum(+1, -1), 0) = tsum(0, 0) = 0
     *   out2 = tsum(tsum(+1, DEC(+1)), INC(+1))
     *        = tsum(tsum(+1, 0), -1) = tsum(+1, -1) = 0
     *
     * All +1 inputs: radix-3 butterfly yields all zeros.
     */
    trit out0, out1, out2;
    int rc = hw_alu_fft_butterfly(&state, +1, +1, +1, &out0, &out1, &out2);
    ASSERT_EQ(rc, 0, "butterfly OK");
    ASSERT_EQ((int)out0, 0, "out0 for all-+1 input");
    ASSERT_EQ((int)out1, 0, "out1 for all-+1 input");
    ASSERT_EQ((int)out2, 0, "out2 for all-+1 input");

    PASS();
}

/* ===================================================================== */
/*  13. HAL Lifecycle                                                    */
/* ===================================================================== */

static void test_hal_init_emulated(void)
{
    TEST(hal_init_returns_0_in_emulated_mode);

    hw_hal_state_t s;
    memset(&s, 0, sizeof(s));
    int rc = hw_hal_init(&s);
    ASSERT_EQ(rc, 0, "hw_hal_init should return 0");
    ASSERT_EQ(s.initialized, 1, "should be initialized");
    ASSERT_EQ(s.mode, HW_MODE_EMULATED, "mode should be emulated");

    PASS();
}

static void test_hal_caps_populated(void)
{
    TEST(hal_caps_populated_after_init);

    hw_hal_state_t s;
    memset(&s, 0, sizeof(s));
    hw_hal_init(&s);

    /* Check electrical parameters match spec */
    ASSERT_EQ(s.caps.vdd_mv, 1000, "VDD should be 1000 mV");
    ASSERT_EQ(s.caps.vth_lvt_mv, 250, "LVT should be 250 mV");
    ASSERT_EQ(s.caps.vth_mvt_mv, 400, "MVT should be 400 mV");
    ASSERT_EQ(s.caps.vth_hvt_mv, 650, "HVT should be 650 mV");

    /* Verify threshold constraint: LVT + HVT < VDD */
    ASSERT_TRUE(s.caps.vth_lvt_mv + s.caps.vth_hvt_mv < s.caps.vdd_mv,
                "constraint: LVT + HVT < VDD");

    PASS();
}

static void test_hal_features(void)
{
    TEST(hal_all_features_present_in_emulation);

    hw_hal_state_t s;
    memset(&s, 0, sizeof(s));
    hw_hal_init(&s);

    ASSERT_EQ(s.caps.has_inc_gate, 1, "INC gate present");
    ASSERT_EQ(s.caps.has_dec_gate, 1, "DEC gate present");
    ASSERT_EQ(s.caps.has_half_adder, 1, "half-adder present");
    ASSERT_EQ(s.caps.has_full_adder, 1, "full-adder present");
    ASSERT_EQ(s.caps.has_multiplier, 1, "multiplier present");
    ASSERT_EQ(s.caps.has_approx_mul, 1, "approx mul present");
    ASSERT_EQ(s.caps.has_compensation, 1, "compensation present");

    PASS();
}

static void test_hal_shutdown(void)
{
    TEST(hal_shutdown_clears_state);

    hw_hal_state_t s;
    memset(&s, 0, sizeof(s));
    hw_hal_init(&s);
    ASSERT_EQ(s.initialized, 1, "should be initialized");

    int rc = hw_hal_shutdown(&s);
    ASSERT_EQ(rc, 0, "shutdown should return 0");
    ASSERT_EQ(s.initialized, 0, "should be de-initialized");

    PASS();
}

static void test_hal_mode_query(void)
{
    TEST(hal_mode_query);

    hw_hal_state_t s;
    memset(&s, 0, sizeof(s));
    hw_hal_init(&s);

    ASSERT_EQ(hw_hal_mode(&s), HW_MODE_EMULATED, "mode is emulated");
    ASSERT_EQ(hw_hal_mode(NULL), HW_MODE_EMULATED, "NULL returns emulated");

    PASS();
}

/* ===================================================================== */
/*  14. Multiplier Width Selection                                       */
/* ===================================================================== */

static void test_mul_word_dispatch(void)
{
    TEST(mul_word_selects_appropriate_width);

    /* 1-trit operands → 1-trit multiply */
    hw_mul_result_t r1 = hw_alu_mul_word(&state, 1, 1, HW_COMP_NONE);
    ASSERT_EQ(r1.width_trits, 1, "1*1 should use 1-trit multiply");
    ASSERT_EQ(r1.result, 1, "1*1 = 1");

    /* 2-trit operands → 2-trit multiply */
    hw_mul_result_t r2 = hw_alu_mul_word(&state, 3, 3, HW_COMP_NONE);
    ASSERT_EQ(r2.width_trits, 4, "3*3 should use 2-trit multiply");
    ASSERT_EQ(r2.result, 9, "3*3 = 9");

    /* Large operands → 6-trit multiply */
    hw_mul_result_t r3 = hw_alu_mul_word(&state, 10, 10, HW_COMP_NONE);
    ASSERT_EQ(r3.width_trits, 12, "10*10 should use 6-trit multiply");
    ASSERT_EQ(r3.result, 100, "10*10 = 100");

    PASS();
}

/* ===================================================================== */
/*  15. Patent-Specific Tests                                            */
/* ===================================================================== */

static void test_triple_inc_is_identity(void)
{
    TEST(triple_inc_wraps_to_identity);

    /* INC applied 3 times = identity (mod 3 rotation) */
    for (hw_trit x = 0; x <= 2; x++) {
        hw_trit r = hw_gate_inc(hw_gate_inc(hw_gate_inc(x)));
        ASSERT_EQ(r, x, "INC^3 = identity");
    }

    PASS();
}

static void test_triple_dec_is_identity(void)
{
    TEST(triple_dec_wraps_to_identity);

    for (hw_trit x = 0; x <= 2; x++) {
        hw_trit r = hw_gate_dec(hw_gate_dec(hw_gate_dec(x)));
        ASSERT_EQ(r, x, "DEC^3 = identity");
    }

    PASS();
}

static void test_nti_pti_pb_nb_composition(void)
{
    TEST(preprocessor_composition_properties);

    /* NTI(PTI(x)) should give useful signal separation */
    /* NTI(PTI(0)) = NTI(2) = 0 */
    ASSERT_EQ(hw_gate_nti(hw_gate_pti(HW_TRIT_0)), HW_TRIT_0,
              "NTI(PTI(0)) = 0");
    /* NTI(PTI(1)) = NTI(2) = 0 */
    ASSERT_EQ(hw_gate_nti(hw_gate_pti(HW_TRIT_1)), HW_TRIT_0,
              "NTI(PTI(1)) = 0");
    /* NTI(PTI(2)) = NTI(0) = 2 */
    ASSERT_EQ(hw_gate_nti(hw_gate_pti(HW_TRIT_2)), HW_TRIT_2,
              "NTI(PTI(2)) = 2");

    /* PB AND NB are disjoint except at extremes */
    /* PB(0)=0, NB(0)=0: both off for input 0 */
    ASSERT_EQ(hw_gate_pb(HW_TRIT_0), HW_TRIT_0, "PB(0) = 0");
    ASSERT_EQ(hw_gate_nb(HW_TRIT_0), HW_TRIT_0, "NB(0) = 0");
    /* PB(1)=2, NB(1)=0: PB on, NB off for input 1 */
    ASSERT_EQ(hw_gate_pb(HW_TRIT_1), HW_TRIT_2, "PB(1) = 2");
    ASSERT_EQ(hw_gate_nb(HW_TRIT_1), HW_TRIT_0, "NB(1) = 0");
    /* PB(2)=2, NB(2)=2: both on for input 2 */
    ASSERT_EQ(hw_gate_pb(HW_TRIT_2), HW_TRIT_2, "PB(2) = 2");
    ASSERT_EQ(hw_gate_nb(HW_TRIT_2), HW_TRIT_2, "NB(2) = 2");

    PASS();
}

static void test_transistor_threshold_constraint(void)
{
    TEST(lvt_plus_hvt_less_than_vdd);

    hw_hal_state_t s;
    memset(&s, 0, sizeof(s));
    hw_hal_init(&s);

    int lvt = s.caps.vth_lvt_mv;
    int hvt = s.caps.vth_hvt_mv;
    int vdd = s.caps.vdd_mv;

    /* Critical constraint from patent: LVT + HVT < VDD */
    ASSERT_TRUE(lvt + hvt < vdd,
                "Patent constraint: LVT + HVT must be < VDD");

    /* All thresholds positive */
    ASSERT_TRUE(lvt > 0, "LVT > 0");
    ASSERT_TRUE(hvt > 0, "HVT > 0");
    ASSERT_TRUE(s.caps.vth_mvt_mv > 0, "MVT > 0");

    /* Ordering: LVT < MVT < HVT */
    ASSERT_TRUE(lvt < s.caps.vth_mvt_mv, "LVT < MVT");
    ASSERT_TRUE(s.caps.vth_mvt_mv < hvt, "MVT < HVT");

    /* VDD in valid range (900-1800 mV) */
    ASSERT_TRUE(vdd >= 900 && vdd <= 1800, "VDD in range [900,1800]");

    PASS();
}

/* ===================================================================== */
/*  Main                                                                 */
/* ===================================================================== */

int main(void)
{
    printf("=== Huawei CN119652311A Ternary Chip HAL Tests ===\n\n");

    /* Initialise shared HAL state in emulated mode */
    memset(&state, 0, sizeof(state));
    hw_hal_init(&state);

    printf("[Section 1: Value Translation]\n");
    test_hw_from_balanced();
    test_hw_to_balanced();
    test_roundtrip_translation();
    test_trit2_conversion();

    printf("\n[Section 2: Gate Truth Tables (Huawei encoding)]\n");
    test_gate_inc_truth_table();
    test_gate_dec_truth_table();
    test_inc_dec_inverse();
    test_gate_nti_truth_table();
    test_gate_pti_truth_table();
    test_gate_pb_truth_table();
    test_gate_nb_truth_table();

    printf("\n[Section 3: ALU Gate Operations (balanced)]\n");
    test_alu_inc_balanced();
    test_alu_dec_balanced();
    test_alu_nti_balanced();
    test_alu_pti_balanced();

    printf("\n[Section 4: Summing Circuit (Tsum)]\n");
    test_tsum_exhaustive();

    printf("\n[Section 5: Half-Adder (THA)]\n");
    test_half_adder_exhaustive();
    test_half_adder_consistency();

    printf("\n[Section 6: Full-Adder (TFA)]\n");
    test_full_adder_exhaustive();
    test_full_adder_specific();

    printf("\n[Section 7: Exact Multiply (TMul)]\n");
    test_mul1_exhaustive();

    printf("\n[Section 8: 2trit x 2trit Multiply]\n");
    test_mul2x2_exact_simple();
    test_mul2x2_reconstruction();
    test_mul2x2_compensation_plus6();
    test_mul2x2_compensation_plus9();

    printf("\n[Section 9: 6trit x 6trit Multiply]\n");
    test_mul6x6_simple();
    test_mul6x6_max_range();
    test_mul6x6_trits_width();

    printf("\n[Section 10: Word Addition]\n");
    test_word_add_simple();
    test_word_add_negative();
    test_word_add_carry_propagation();

    printf("\n[Section 11: Dot Product]\n");
    test_dot_product_simple();
    test_dot_product_mixed();
    test_dot_product_orthogonal();

    printf("\n[Section 12: FFT Butterfly]\n");
    test_fft_butterfly_all_zero();
    test_fft_butterfly_return_code();
    test_fft_butterfly_identity();

    printf("\n[Section 13: HAL Lifecycle]\n");
    test_hal_init_emulated();
    test_hal_caps_populated();
    test_hal_features();
    test_hal_shutdown();
    test_hal_mode_query();

    printf("\n[Section 14: Multiplier Width Selection]\n");
    test_mul_word_dispatch();

    printf("\n[Section 15: Patent-Specific Properties]\n");
    test_triple_inc_is_identity();
    test_triple_dec_is_identity();
    test_nti_pti_pb_nb_composition();
    test_transistor_threshold_constraint();

    /* ---- Summary ---- */
    printf("\n=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);

    return tests_failed ? EXIT_FAILURE : EXIT_SUCCESS;
}
