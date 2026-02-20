/*
 * test_trit_edge_cases.c - Additional edge case tests for balanced ternary operations
 *
 * Tests: Extreme values, overflow/underflow, precision issues
 */

#include "../include/test_harness.h"
#include "../include/ternary.h"
#include <math.h>

/* ---- Extreme value tests ---- */

TEST(test_trit_word_max_value) {
    trit_word w;
    /* Maximum representable value in WORD_SIZE (9) trits: (3^9-1)/2 = 9841 */
    int max_val = ((int)pow(3, WORD_SIZE) - 1) / 2;
    int_to_trit_word(max_val, w);
    ASSERT_EQ(trit_word_to_int(w), max_val);
}

TEST(test_trit_word_min_value) {
    trit_word w;
    /* Minimum representable value: -(3^9-1)/2 = -9841 */
    int min_val = -((int)pow(3, WORD_SIZE) - 1) / 2;
    int_to_trit_word(min_val, w);
    ASSERT_EQ(trit_word_to_int(w), min_val);
}

TEST(test_trit_word_overflow) {
    trit_word a, b, res;
    int max_val = ((int)pow(3, WORD_SIZE) - 1) / 2;  /* 9841 */
    int_to_trit_word(max_val, a);
    int_to_trit_word(1, b);
    trit_word_add(a, b, res);
    /* 9841+1=9842 overflows 9-trit range: wraps to -(9841) + 1 = -9840 */
    int result = trit_word_to_int(res);
    ASSERT_NEQ(result, max_val + 1);  /* Must not produce correct answer */
    ASSERT_TRUE(result >= -max_val && result <= max_val);  /* Must stay in range */
}

TEST(test_trit_word_underflow) {
    trit_word a, b, res;
    int min_val = -((int)pow(3, WORD_SIZE) - 1) / 2;  /* -9841 */
    int_to_trit_word(min_val, a);
    int_to_trit_word(-1, b);
    trit_word_add(a, b, res);
    /* -9841+(-1) underflows 9-trit range */
    int result = trit_word_to_int(res);
    ASSERT_NEQ(result, min_val - 1);  /* Must not produce correct answer */
    ASSERT_TRUE(result >= min_val && result <= -min_val);  /* Must stay in range */
}

/* ---- Precision and rounding tests ---- */

TEST(test_trit_precision_loss) {
    trit_word w;
    // Test values that might lose precision in ternary
    int vals[] = {7, 13, 19, 31, 43}; // Numbers not powers of 3
    for (int i = 0; i < 5; i++) {
        int_to_trit_word(vals[i], w);
        int back = trit_word_to_int(w);
        ASSERT_EQ(back, vals[i]); // Should be exact for small values
    }
}

TEST(test_trit_large_mul_precision) {
    trit_word a, b, res;
    int_to_trit_word(10, a);
    int_to_trit_word(10, b);
    trit_word_mul(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 100); // 10 * 10 = 100
}

/* ---- Carry propagation tests ---- */

TEST(test_trit_add_carry_chain) {
    trit_word a, b, res;
    // Create a word that will cause carry propagation
    int_to_trit_word(364, a); // 3^5 + 3^4 + 3^3 + 3^2 + 3^1 + 3^0 = 364 in decimal
    int_to_trit_word(1, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 365);
}

TEST(test_trit_sub_carry_chain) {
    trit_word a, b, res;
    int_to_trit_word(365, a);
    int_to_trit_word(1, b);
    trit_word_sub(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 364);
}

/* ---- Boundary condition tests ---- */

TEST(test_trit_zero_operations) {
    trit_word zero, val, res;
    int_to_trit_word(0, zero);
    int_to_trit_word(42, val);

    trit_word_add(zero, val, res);
    ASSERT_EQ(trit_word_to_int(res), 42);

    trit_word_mul(zero, val, res);
    ASSERT_EQ(trit_word_to_int(res), 0);
}

TEST(test_trit_identity_operations) {
    trit_word one, val, res;
    int_to_trit_word(1, one);
    int_to_trit_word(42, val);

    trit_word_mul(one, val, res);
    ASSERT_EQ(trit_word_to_int(res), 42);
}

int main(void) {
    TEST_SUITE_BEGIN("Trit Edge Cases");

    RUN_TEST(test_trit_word_max_value);
    RUN_TEST(test_trit_word_min_value);
    RUN_TEST(test_trit_word_overflow);
    RUN_TEST(test_trit_word_underflow);
    RUN_TEST(test_trit_precision_loss);
    RUN_TEST(test_trit_large_mul_precision);
    RUN_TEST(test_trit_add_carry_chain);
    RUN_TEST(test_trit_sub_carry_chain);
    RUN_TEST(test_trit_zero_operations);
    RUN_TEST(test_trit_identity_operations);

    TEST_SUITE_END();
}