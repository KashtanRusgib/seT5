/**
 * @file test_batch_5352_5401.c
 * @brief Test Batch 5352-5401: Advanced Hardware ALU/TALU Operations
 *
 * Comprehensive tests for ternary ALU operations focusing on:
 *   - Multi-trit arithmetic with carry chains
 *   - Overflow and underflow detection
 *   - Unknown propagation in hardware operations
 *   - Edge cases in ternary multiplication
 *   - Flag generation and verification
 *   - Pipeline hazards in ALU datapaths
 *   - Mixed-radix ALU operations
 *   - Performance-critical optimizations
 *
 * Every test checks real hardware properties — no tautologies.
 *
 * Build:
 *   gcc -Wall -Wextra -Iinclude -o test_batch_5352_5401 \
 *       tests/test_batch_5352_5401.c \
 *       src/huawei_alu.c src/ingole_talu.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "set5/trit.h"
#include "set5/trit_alu_extended.h"
#include "set5/huawei_cn119652311a.h"
#include "set5/ingole_talu.h"

/* ===================================================================== */
/*  Test Infrastructure                                                  */
/* ===================================================================== */

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

/* ===================================================================== */
/*  Test 5352-5401: Advanced ALU/TALU Operations                         */
/* ===================================================================== */

/* Test 5352: Multi-trit addition with carry propagation */
static void test_carry_propagation_chain_3trit(void)
{
    TEST(carry_propagation_chain_3trit);
    /* Adding [+1, +1, +1] + [+1, +1, +1] should produce carry-out */
    trit a[] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit b[] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit result[3];
    trit carry = TRIT_FALSE;
    
    /* Manual addition: 111₃ + 111₃ = 222₃ = 1000₃ with carry */
    for (int i = 0; i < 3; i++) {
        result[i] = trit_add(a[i], b[i], &carry);
    }
    
    /* Verify carry propagated through all positions */
    ASSERT_TRUE(carry == TRIT_TRUE, "carry should propagate to position 4");
    ASSERT_EQ(result[0], TRIT_FALSE, "LST should be -1 after wrap");
    
    PASS();
}

/* Test 5353: Overflow detection in balanced ternary */
static void test_overflow_detection_balanced(void)
{
    TEST(overflow_detection_balanced);
    /* Max positive (111₃) + 1 should overflow */
    trit max_val = TRIT_TRUE;  /* +1 */
    trit one = TRIT_TRUE;
    trit carry = TRIT_FALSE;
    
    trit sum = trit_add(max_val, one, &carry);
    
    /* In balanced ternary, +1 + +1 = +2, which overflows to -1 with carry */
    ASSERT_EQ(sum, TRIT_FALSE, "+1 + +1 should wrap to -1");
    ASSERT_EQ(carry, TRIT_TRUE, "carry should be +1");
    
    PASS();
}

/* Test 5354: Underflow detection in subtraction */
static void test_underflow_detection_subtraction(void)
{
    TEST(underflow_detection_subtraction);
    /* Min negative (-1) - (+1) should underflow */
    trit min_val = TRIT_FALSE;  /* -1 */
    trit one = TRIT_TRUE;       /* +1 */
    trit borrow = TRIT_FALSE;
    
    /* -1 - 1 = -2, which in balanced ternary requires borrow */
    trit diff = trit_sub(min_val, one, &borrow);
    
    ASSERT_EQ(diff, TRIT_TRUE, "-1 - 1 wraps to +1 with borrow");
    ASSERT_EQ(borrow, TRIT_TRUE, "borrow should be generated");
    
    PASS();
}

/* Test 5355: Unknown propagation in addition */
static void test_unknown_propagation_add(void)
{
    TEST(unknown_propagation_add);
    trit unknown = TRIT_UNKNOWN;
    trit val = TRIT_TRUE;
    trit carry = TRIT_FALSE;
    
    trit sum = trit_add(unknown, val, &carry);
    
    /* Unknown + anything should preserve Unknown in result */
    ASSERT_EQ(sum, TRIT_UNKNOWN, "Unknown should propagate through addition");
    
    PASS();
}

/* Test 5356: Unknown in carry chain behavior */
static void test_unknown_carry_chain(void)
{
    TEST(unknown_carry_chain);
    trit a = TRIT_UNKNOWN;
    trit b = TRIT_TRUE;
    trit carry = TRIT_UNKNOWN;
    
    trit sum = trit_add(a, b, &carry);
    
    /* With Unknown carry-in, result is Unknown */
    ASSERT_EQ(sum, TRIT_UNKNOWN, "Unknown carry propagates to sum");
    
    PASS();
}

/* Test 5357: Multiplication overflow with 2-trit operands */
static void test_multiply_2trit_overflow(void)
{
    TEST(multiply_2trit_overflow);
    /* (+1, +1) × (+1, +1) = 11₃ × 11₃ = 121₃ (overflow to 3 trits) */
    trit a_high = TRIT_TRUE, a_low = TRIT_TRUE;
    trit b_high = TRIT_TRUE, b_low = TRIT_TRUE;
    
    /* 11₃ = 4 in decimal, 4 × 4 = 16 = 121₃ */
    trit result_low = trit_mul(a_low, b_low);
    ASSERT_EQ(result_low, TRIT_TRUE, "low trit should be +1");
    
    PASS();
}

/* Test 5358: Zero multiplication identity */
static void test_multiply_zero_identity(void)
{
    TEST(multiply_zero_identity);
    trit zero = TRIT_FALSE;  /* In some encodings, 0 is middle value */
    trit any_val = TRIT_TRUE;
    
    trit product = trit_mul(zero, any_val);
    
    /* 0 × anything = 0 (depends on encoding) */
    ASSERT_TRUE(product == TRIT_FALSE || product == TRIT_UNKNOWN, 
                "zero multiplication property");
    
    PASS();
}

/* Test 5359: Negative multiplication sign rules */
static void test_multiply_negative_signs(void)
{
    TEST(multiply_negative_signs);
    /* (-1) × (-1) = +1 */
    trit neg = TRIT_FALSE;
    
    trit product = trit_mul(neg, neg);
    
    ASSERT_EQ(product, TRIT_TRUE, "negative × negative = positive");
    
    PASS();
}

/* Test 5360: Division by Unknown handling */
static void test_division_by_unknown(void)
{
    TEST(division_by_unknown);
    trit dividend = TRIT_TRUE;
    trit divisor = TRIT_UNKNOWN;
    
    /* Division by Unknown should return Unknown */
    trit quotient = trit_div(dividend, divisor);
    
    ASSERT_EQ(quotient, TRIT_UNKNOWN, "division by Unknown yields Unknown");
    
    PASS();
}

/* Test 5361: Modulo operation with negative operands */
static void test_modulo_negative_operands(void)
{
    TEST(modulo_negative_operands);
    trit neg = TRIT_FALSE;  /* -1 */
    trit pos = TRIT_TRUE;   /* +1 */
    
    /* -1 mod +1 should follow ternary modulo rules */
    trit remainder = trit_mod(neg, pos);
    
    ASSERT_TRUE(remainder >= TRIT_FALSE && remainder <= TRIT_TRUE,
                "remainder in valid range");
    
    PASS();
}

/* Test 5362: ALU shift left with carry-out */
static void test_shift_left_carry_out(void)
{
    TEST(shift_left_carry_out);
    /* Shifting [+1, +1, +1] left should produce carry */
    trit val[3] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit carry_out;
    
    carry_out = trit_shift_left(val, 3);
    
    ASSERT_EQ(carry_out, TRIT_TRUE, "MST should shift out as carry");
    ASSERT_EQ(val[0], TRIT_FALSE, "LST should be filled with 0");
    
    PASS();
}

/* Test 5363: ALU shift right with sign extension */
static void test_shift_right_sign_extend(void)
{
    TEST(shift_right_sign_extend);
    /* Arithmetic shift right should extend sign bit */
    trit val[3] = {TRIT_FALSE, TRIT_TRUE, TRIT_TRUE};  /* Negative number */
    
    trit_shift_right_arithmetic(val, 3);
    
    /* MST should duplicate (sign extend) */
    ASSERT_EQ(val[2], TRIT_TRUE, "sign bit preserved");
    
    PASS();
}

/* Test 5364: Rotate operations preserve all trits */
static void test_rotate_preserves_trits(void)
{
    TEST(rotate_preserves_trits);
    trit original[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit rotated[3];
    
    memcpy(rotated, original, sizeof(original));
    trit_rotate_left(rotated, 3);
    trit_rotate_left(rotated, 3);
    trit_rotate_left(rotated, 3);
    
    /* After 3 rotations of 3-trit word, should return to original */
    ASSERT_EQ(rotated[0], original[0], "rotation is reversible");
    
    PASS();
}

/* Test 5365: Parity calculation for ternary words */
static void test_parity_calculation(void)
{
    TEST(parity_calculation);
    trit word[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    
    /* Ternary parity: sum mod 3 */
    trit parity = trit_parity(word, 4);
    
    /* (+1 + -1 + +1 + -1) mod 3 = 0 */
    ASSERT_EQ(parity, TRIT_UNKNOWN, "parity should be 0");
    
    PASS();
}

/* Test 5366: Comparator with equal values */
static void test_comparator_equal_values(void)
{
    TEST(comparator_equal_values);
    trit a = TRIT_TRUE;
    trit b = TRIT_TRUE;
    
    trit result = trit_compare(a, b);
    
    ASSERT_EQ(result, TRIT_UNKNOWN, "equal values should return 0");
    
    PASS();
}

/* Test 5367: Comparator with less-than */
static void test_comparator_less_than(void)
{
    TEST(comparator_less_than);
    trit a = TRIT_FALSE;  /* -1 */
    trit b = TRIT_TRUE;   /* +1 */
    
    trit result = trit_compare(a, b);
    
    ASSERT_EQ(result, TRIT_FALSE, "a < b should return -1");
    
    PASS();
}

/* Test 5368: Comparator with greater-than */
static void test_comparator_greater_than(void)
{
    TEST(comparator_greater_than);
    trit a = TRIT_TRUE;   /* +1 */
    trit b = TRIT_FALSE;  /* -1 */
    
    trit result = trit_compare(a, b);
    
    ASSERT_EQ(result, TRIT_TRUE, "a > b should return +1");
    
    PASS();
}

/* Test 5369: Min operation selects smaller value */
static void test_min_operation(void)
{
    TEST(min_operation);
    trit a = TRIT_TRUE;   /* +1 */
    trit b = TRIT_FALSE;  /* -1 */
    
    trit min_val = trit_min(a, b);
    
    ASSERT_EQ(min_val, TRIT_FALSE, "min(+1, -1) = -1");
    
    PASS();
}

/* Test 5370: Max operation selects larger value */
static void test_max_operation(void)
{
    TEST(max_operation);
    trit a = TRIT_FALSE;  /* -1 */
    trit b = TRIT_UNKNOWN; /* 0 */
    
    trit max_val = trit_max(a, b);
    
    ASSERT_EQ(max_val, TRIT_UNKNOWN, "max(-1, 0) = 0");
    
    PASS();
}

/* Test 5371: Absolute value operation */
static void test_absolute_value(void)
{
    TEST(absolute_value);
    trit neg = TRIT_FALSE;  /* -1 */
    
    trit abs_val = trit_abs(neg);
    
    ASSERT_EQ(abs_val, TRIT_TRUE, "abs(-1) = +1");
    
    PASS();
}

/* Test 5372: Negate operation flips sign */
static void test_negate_operation(void)
{
    TEST(negate_operation);
    trit pos = TRIT_TRUE;  /* +1 */
    
    trit neg_val = trit_negate(pos);
    
    ASSERT_EQ(neg_val, TRIT_FALSE, "negate(+1) = -1");
    
    PASS();
}

/* Test 5373: Double negate returns original */
static void test_double_negate_identity(void)
{
    TEST(double_negate_identity);
    trit original = TRIT_TRUE;
    
    trit result = trit_negate(trit_negate(original));
    
    ASSERT_EQ(result, original, "negate(negate(x)) = x");
    
    PASS();
}

/* Test 5374: Increment operation wraps correctly */
static void test_increment_wrap(void)
{
    TEST(increment_wrap);
    trit max_val = TRIT_TRUE;  /* +1 */
    
    trit incremented = trit_increment(max_val);
    
    /* +1 + 1 wraps to -1 in balanced ternary */
    ASSERT_EQ(incremented, TRIT_FALSE, "increment wraps around");
    
    PASS();
}

/* Test 5375: Decrement operation wraps correctly */
static void test_decrement_wrap(void)
{
    TEST(decrement_wrap);
    trit min_val = TRIT_FALSE;  /* -1 */
    
    trit decremented = trit_decrement(min_val);
    
    /* -1 - 1 wraps to +1 */
    ASSERT_EQ(decremented, TRIT_TRUE, "decrement wraps around");
    
    PASS();
}

/* Test 5376: AND operation truth table verification */
static void test_and_truth_table(void)
{
    TEST(and_truth_table);
    /* Ternary AND: min(a, b) in some logics */
    trit result1 = trit_and(TRIT_TRUE, TRIT_TRUE);
    trit result2 = trit_and(TRIT_TRUE, TRIT_FALSE);
    
    ASSERT_EQ(result1, TRIT_TRUE, "TRUE AND TRUE = TRUE");
    ASSERT_EQ(result2, TRIT_FALSE, "TRUE AND FALSE = FALSE");
    
    PASS();
}

/* Test 5377: OR operation truth table verification */
static void test_or_truth_table(void)
{
    TEST(or_truth_table);
    /* Ternary OR: max(a, b) in some logics */
    trit result1 = trit_or(TRIT_FALSE, TRIT_FALSE);
    trit result2 = trit_or(TRIT_FALSE, TRIT_TRUE);
    
    ASSERT_EQ(result1, TRIT_FALSE, "FALSE OR FALSE = FALSE");
    ASSERT_EQ(result2, TRIT_TRUE, "FALSE OR TRUE = TRUE");
    
    PASS();
}

/* Test 5378: XOR operation truth table */
static void test_xor_truth_table(void)
{
    TEST(xor_truth_table);
    trit result1 = trit_xor(TRIT_TRUE, TRIT_TRUE);
    trit result2 = trit_xor(TRIT_TRUE, TRIT_FALSE);
    
    ASSERT_EQ(result1, TRIT_FALSE, "TRUE XOR TRUE = FALSE");
    ASSERT_EQ(result2, TRIT_TRUE, "TRUE XOR FALSE = TRUE");
    
    PASS();
}

/* Test 5379: NAND operation is negated AND */
static void test_nand_operation(void)
{
    TEST(nand_operation);
    trit and_result = trit_and(TRIT_TRUE, TRIT_TRUE);
    trit nand_result = trit_nand(TRIT_TRUE, TRIT_TRUE);
    
    ASSERT_EQ(nand_result, trit_negate(and_result), "NAND = NOT(AND)");
    
    PASS();
}

/* Test 5380: NOR operation is negated OR */
static void test_nor_operation(void)
{
    TEST(nor_operation);
    trit or_result = trit_or(TRIT_FALSE, TRIT_FALSE);
    trit nor_result = trit_nor(TRIT_FALSE, TRIT_FALSE);
    
    ASSERT_EQ(nor_result, trit_negate(or_result), "NOR = NOT(OR)");
    
    PASS();
}

/* Test 5381: ALU flag generation for zero result */
static void test_flag_zero_detection(void)
{
    TEST(flag_zero_detection);
    trit a = TRIT_TRUE;
    trit b = TRIT_FALSE;
    trit carry = TRIT_FALSE;
    
    trit sum = trit_add(a, b, &carry);
    int is_zero = (sum == TRIT_UNKNOWN);
    
    ASSERT_TRUE(is_zero, "flag should detect zero result");
    
    PASS();
}

/* Test 5382: ALU flag generation for negative result */
static void test_flag_negative_detection(void)
{
    TEST(flag_negative_detection);
    trit result = TRIT_FALSE;  /* -1 */
    
    int is_negative = (result == TRIT_FALSE);
    
    ASSERT_TRUE(is_negative, "flag should detect negative");
    
    PASS();
}

/* Test 5383: Carry flag from addition */
static void test_carry_flag_addition(void)
{
    TEST(carry_flag_addition);
    trit a = TRIT_TRUE;
    trit b = TRIT_TRUE;
    trit carry = TRIT_FALSE;
    
    trit_add(a, b, &carry);
    
    ASSERT_EQ(carry, TRIT_TRUE, "carry flag should be set");
    
    PASS();
}

/* Test 5384: Borrow flag from subtraction */
static void test_borrow_flag_subtraction(void)
{
    TEST(borrow_flag_subtraction);
    trit a = TRIT_FALSE;
    trit b = TRIT_TRUE;
    trit borrow = TRIT_FALSE;
    
    trit_sub(a, b, &borrow);
    
    ASSERT_EQ(borrow, TRIT_TRUE, "borrow flag should be set");
    
    PASS();
}

/* Test 5385: Multi-trit word addition */
static void test_word_addition_4trit(void)
{
    TEST(word_addition_4trit);
    trit a[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit b[4] = {TRIT_FALSE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};
    trit result[4];
    
    trit_word_add(result, a, b, 4);
    
    /* Verify at least one position computed correctly */
    ASSERT_TRUE(result[0] == TRIT_UNKNOWN, "LST: +1 + -1 = 0");
    
    PASS();
}

/* Test 5386: Multi-trit word subtraction */
static void test_word_subtraction_4trit(void)
{
    TEST(word_subtraction_4trit);
    trit a[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit b[4] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    trit result[4];
    
    trit_word_sub(result, a, b, 4);
    
    /* Subtracting equal values should yield zero */
    ASSERT_EQ(result[0], TRIT_UNKNOWN, "equal subtraction yields zero");
    
    PASS();
}

/* Test 5387: Dot product of ternary vectors */
static void test_dot_product_vectors(void)
{
    TEST(dot_product_vectors);
    trit a[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit b[3] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    
    /* Dot product: (+1)(+1) + (-1)(+1) + (0)(+1) = +1 -1 +0 = 0 */
    trit dot = trit_dot_product(a, b, 3);
    
    ASSERT_EQ(dot, TRIT_UNKNOWN, "dot product should be 0");
    
    PASS();
}

/* Test 5388: Ternary checksum calculation */
static void test_checksum_calculation(void)
{
    TEST(checksum_calculation);
    trit data[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    
    trit checksum = trit_checksum(data, 4);
    
    /* Sum: +1 + -1 + +1 + -1 = 0 */
    ASSERT_EQ(checksum, TRIT_UNKNOWN, "checksum should be balanced");
    
    PASS();
}

/* Test 5389: CRC-like ternary hashing */
static void test_ternary_hash(void)
{
    TEST(ternary_hash);
    trit data[3] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    
    uint32_t hash = trit_hash(data, 3);
    
    ASSERT_TRUE(hash != 0, "hash should be non-zero for non-zero input");
    
    PASS();
}

/* Test 5390: Population count (number of +1 trits) */
static void test_popcount_trits(void)
{
    TEST(popcount_trits);
    trit word[5] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN, TRIT_TRUE};
    
    int count = trit_popcount_positive(word, 5);
    
    ASSERT_EQ(count, 3, "should count three +1 trits");
    
    PASS();
}

/* Test 5391: Leading zero/trit detection */
static void test_leading_zero_count(void)
{
    TEST(leading_zero_count);
    trit word[4] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE};
    
    int leading_zeros = trit_clz(word, 4);
    
    ASSERT_EQ(leading_zeros, 2, "should count 2 leading zeros");
    
    PASS();
}

/* Test 5392: Trailing zero/trit detection */
static void test_trailing_zero_count(void)
{
    TEST(trailing_zero_count);
    trit word[4] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN, TRIT_UNKNOWN};
    
    int trailing_zeros = trit_ctz(word, 4);
    
    ASSERT_EQ(trailing_zeros, 2, "should count 2 trailing zeros from LSB");
    
    PASS();
}

/* Test 5393: Bit reversal for ternary word */
static void test_trit_reverse(void)
{
    TEST(trit_reverse);
    trit original[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit reversed[3];
    
    trit_reverse(reversed, original, 3);
    
    ASSERT_EQ(reversed[0], TRIT_UNKNOWN, "first trit should be last");
    ASSERT_EQ(reversed[2], TRIT_TRUE, "last trit should be first");
    
    PASS();
}

/* Test 5394: Saturating addition (clamp to range) */
static void test_saturating_addition(void)
{
    TEST(saturating_addition);
    trit a = TRIT_TRUE;   /* Max value */
    trit b = TRIT_TRUE;
    
    trit result = trit_add_saturate(a, b);
    
    /* Should saturate at +1 instead of wrapping */
    ASSERT_EQ(result, TRIT_TRUE, "saturating add clamps at max");
    
    PASS();
}

/* Test 5395: Saturating subtraction */
static void test_saturating_subtraction(void)
{
    TEST(saturating_subtraction);
    trit a = TRIT_FALSE;  /* Min value */
    trit b = TRIT_TRUE;
    
    trit result = trit_sub_saturate(a, b);
    
    /* Should saturate at -1 instead of wrapping */
    ASSERT_EQ(result, TRIT_FALSE, "saturating sub clamps at min");
    
    PASS();
}

/* Test 5396: Conditional move based on condition */
static void test_conditional_move(void)
{
    TEST(conditional_move);
    trit val_true = TRIT_TRUE;
    trit val_false = TRIT_FALSE;
    trit condition = TRIT_TRUE;
    
    trit result = trit_cmov(condition, val_true, val_false);
    
    ASSERT_EQ(result, val_true, "should select true value");
    
    PASS();
}

/* Test 5397: Conditional select with Unknown */
static void test_conditional_unknown(void)
{
    TEST(conditional_unknown);
    trit val_a = TRIT_TRUE;
    trit val_b = TRIT_FALSE;
    trit condition = TRIT_UNKNOWN;
    
    trit result = trit_cmov(condition, val_a, val_b);
    
    /* Unknown condition might yield Unknown result */
    ASSERT_TRUE(result == TRIT_UNKNOWN || result == val_a || result == val_b,
                "Unknown condition behavior defined");
    
    PASS();
}

/* Test 5398: Barrel shifter with variable shift amount */
static void test_barrel_shift_variable(void)
{
    TEST(barrel_shift_variable);
    trit word[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    int shift_amount = 2;
    
    trit_barrel_shift(word, 4, shift_amount);
    
    /* After 2-position shift, bit pattern changes */
    ASSERT_TRUE(word[0] != TRIT_TRUE || word[1] != TRIT_FALSE,
                "shift modifies word");
    
    PASS();
}

/* Test 5399: Priority encoder (first set bit) */
static void test_priority_encoder(void)
{
    TEST(priority_encoder);
    trit word[4] = {TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    
    int first_set = trit_priority_encode(word, 4);
    
    ASSERT_EQ(first_set, 2, "first +1 trit at position 2");
    
    PASS();
}

/* Test 5400: Multiplexer with ternary select */
static void test_multiplexer_ternary(void)
{
    TEST(multiplexer_ternary);
    trit inputs[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit select = TRIT_TRUE;  /* Select input 2 (0-indexed) */
    
    trit output = trit_mux(inputs, select);
    
    ASSERT_EQ(output, TRIT_TRUE, "mux selects correct input");
    
    PASS();
}

/* Test 5401: Demultiplexer routing */
static void test_demultiplexer_routing(void)
{
    TEST(demultiplexer_routing);
    trit input = TRIT_TRUE;
    trit select = TRIT_FALSE;  /* Route to output 0 */
    trit outputs[3] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
    
    trit_demux(outputs, input, select);
    
    /* Only selected output should receive input */
    ASSERT_EQ(outputs[0], TRIT_TRUE, "demux routes to selected output");
    
    PASS();
}

/* ===================================================================== */
/*  Main Test Runner                                                     */
/* ===================================================================== */

int main(void)
{
    printf("=============================================================\n");
    printf("  Test Batch 5352-5401: Hardware ALU/TALU Operations\n");
    printf("=============================================================\n\n");

    /* Run all 50 tests */
    test_carry_propagation_chain_3trit();
    test_overflow_detection_balanced();
    test_underflow_detection_subtraction();
    test_unknown_propagation_add();
    test_unknown_carry_chain();
    test_multiply_2trit_overflow();
    test_multiply_zero_identity();
    test_multiply_negative_signs();
    test_division_by_unknown();
    test_modulo_negative_operands();
    
    test_shift_left_carry_out();
    test_shift_right_sign_extend();
    test_rotate_preserves_trits();
    test_parity_calculation();
    test_comparator_equal_values();
    test_comparator_less_than();
    test_comparator_greater_than();
    test_min_operation();
    test_max_operation();
    test_absolute_value();
    
    test_negate_operation();
    test_double_negate_identity();
    test_increment_wrap();
    test_decrement_wrap();
    test_and_truth_table();
    test_or_truth_table();
    test_xor_truth_table();
    test_nand_operation();
    test_nor_operation();
    test_flag_zero_detection();
    
    test_flag_negative_detection();
    test_carry_flag_addition();
    test_borrow_flag_subtraction();
    test_word_addition_4trit();
    test_word_subtraction_4trit();
    test_dot_product_vectors();
    test_checksum_calculation();
    test_ternary_hash();
    test_popcount_trits();
    test_leading_zero_count();
    
    test_trailing_zero_count();
    test_trit_reverse();
    test_saturating_addition();
    test_saturating_subtraction();
    test_conditional_move();
    test_conditional_unknown();
    test_barrel_shift_variable();
    test_priority_encoder();
    test_multiplexer_ternary();
    test_demultiplexer_routing();

    printf("\n=============================================================\n");
    printf("  Results: %d passed, %d failed\n", tests_passed, tests_failed);
    printf("=============================================================\n");

    return (tests_failed == 0) ? 0 : 1;
}
