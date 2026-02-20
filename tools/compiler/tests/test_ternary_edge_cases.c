/* tests/test_ternary_edge_cases.c - Edge cases in ternary arithmetic */
#include <stdio.h>
#include <limits.h>
#include "../include/test_harness.h"
#include "../include/ternary.h"

TEST(test_trit_overflow) {
    // Test overflow conditions in trit arithmetic
    trit result, carry;

    // 1 + 1 = -1 with carry 1
    carry = TRIT_Z;
    result = trit_add(TRIT_P, TRIT_P, &carry);
    ASSERT_EQ(result, TRIT_N);
    ASSERT_EQ(carry, TRIT_P);

    // -1 + -1 = 1 with carry -1
    carry = TRIT_Z;
    result = trit_add(TRIT_N, TRIT_N, &carry);
    ASSERT_EQ(result, TRIT_P);
    ASSERT_EQ(carry, TRIT_N);

    // Test multiplication overflow
    // 1 * 1 = 1 (no overflow)
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_P), TRIT_P);
    // -1 * -1 = 1 (no overflow)
    ASSERT_EQ(trit_mul(TRIT_N, TRIT_N), TRIT_P);
    // 1 * -1 = -1 (no overflow)
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_N), TRIT_N);
}

TEST(test_trit_underflow) {
    // Test underflow conditions
    trit result, carry;

    // -1 - 1 = 1 with borrow -1 (underflow)
    // trit_sub(a, b, &borrow) does a + (-b) using borrow as carry in/out
    carry = TRIT_Z;
    result = trit_sub(TRIT_N, TRIT_P, &carry);
    // -1 + (-1) with carry 0 = 1 with carry -1
    ASSERT_EQ(result, TRIT_P);
    ASSERT_EQ(carry, TRIT_N);

    // Test division by zero should be handled
    // Note: trit_div might not be implemented, skip if not
}

TEST(test_precision_loss) {
    /* Verify that all small integers survive balanced ternary round-trip */
    trit_word w;
    int vals[] = {7, 13, 19, 31, 43, 100, -100, 364, -364};
    for (int i = 0; i < 9; i++) {
        int_to_trit_word(vals[i], w);
        int back = trit_word_to_int(w);
        ASSERT_EQ(back, vals[i]);
    }

    /* Verify word-level add correctness for non-power-of-3 values */
    trit_word a, b, res;
    int_to_trit_word(19, a);
    int_to_trit_word(31, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 50);
}

TEST(test_extreme_values) {
    // Test with extreme ternary values
    trit t_max = TRIT_P;
    trit t_min = TRIT_N;
    trit t_zero = TRIT_Z;
    trit carry = TRIT_Z;

    // Test all combinations of operations
    ASSERT_EQ(trit_add(t_max, t_zero, &carry), t_max);
    ASSERT_EQ(carry, TRIT_Z);
    carry = TRIT_Z;
    ASSERT_EQ(trit_add(t_min, t_zero, &carry), t_min);
    ASSERT_EQ(carry, TRIT_Z);
    ASSERT_EQ(trit_mul(t_max, t_zero), t_zero);
    ASSERT_EQ(trit_mul(t_min, t_zero), t_zero);
}

TEST(test_balanced_ternary_properties) {
    // Test mathematical properties of balanced ternary
    // -1 + 1 = 0
    trit carry = TRIT_Z;
    trit sum = trit_add(TRIT_N, TRIT_P, &carry);
    ASSERT_EQ(sum, TRIT_Z);
    ASSERT_EQ(carry, TRIT_Z);

    // Test that every integer has unique representation
    // This is more of a theoretical test
}

int main(void) {
    TEST_SUITE_BEGIN("Ternary Arithmetic Edge Cases");

    RUN_TEST(test_trit_overflow);
    RUN_TEST(test_trit_underflow);
    RUN_TEST(test_precision_loss);
    RUN_TEST(test_extreme_values);
    RUN_TEST(test_balanced_ternary_properties);

    TEST_SUITE_END();
}