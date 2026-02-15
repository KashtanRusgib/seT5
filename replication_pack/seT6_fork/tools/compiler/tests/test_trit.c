/*
 * test_trit.c - Unit tests for balanced ternary trit operations
 *
 * Tests: trit_add, trit_mul, trit_min, trit_max
 * Coverage: All valid trit input combinations (-1, 0, +1)
 */

#include "../include/test_harness.h"
#include "../include/ternary.h"

/* ---- trit_mul tests ---- */

TEST(test_mul_pos_pos) {
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_P), TRIT_P);   //  1 *  1 =  1
}

TEST(test_mul_pos_neg) {
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_N), TRIT_N);    //  1 * -1 = -1
}

TEST(test_mul_neg_neg) {
    ASSERT_EQ(trit_mul(TRIT_N, TRIT_N), TRIT_P);    // -1 * -1 =  1
}

TEST(test_mul_zero_any) {
    ASSERT_EQ(trit_mul(TRIT_Z, TRIT_P), TRIT_Z);    //  0 *  1 =  0
    ASSERT_EQ(trit_mul(TRIT_Z, TRIT_N), TRIT_Z);    //  0 * -1 =  0
    ASSERT_EQ(trit_mul(TRIT_Z, TRIT_Z), TRIT_Z);    //  0 *  0 =  0
}

TEST(test_mul_neg_pos) {
    ASSERT_EQ(trit_mul(TRIT_N, TRIT_P), TRIT_N);    // -1 *  1 = -1
}

/* ---- trit_add tests ---- */

TEST(test_add_no_carry_basic) {
    trit carry = TRIT_Z;

    /* 1 + 0 = 1, no carry */
    ASSERT_EQ(trit_add(TRIT_P, TRIT_Z, &carry), TRIT_P);
    ASSERT_EQ(carry, TRIT_Z);

    /* 0 + 0 = 0, no carry */
    carry = TRIT_Z;
    ASSERT_EQ(trit_add(TRIT_Z, TRIT_Z, &carry), TRIT_Z);
    ASSERT_EQ(carry, TRIT_Z);

    /* -1 + 0 = -1, no carry */
    carry = TRIT_Z;
    ASSERT_EQ(trit_add(TRIT_N, TRIT_Z, &carry), TRIT_N);
    ASSERT_EQ(carry, TRIT_Z);
}

TEST(test_add_cancel) {
    trit carry = TRIT_Z;

    /* 1 + (-1) = 0, no carry */
    ASSERT_EQ(trit_add(TRIT_P, TRIT_N, &carry), TRIT_Z);
    ASSERT_EQ(carry, TRIT_Z);
}

TEST(test_add_positive_overflow) {
    trit carry = TRIT_Z;

    /* 1 + 1 = 2 → balanced ternary: -1 with carry +1 */
    trit result = trit_add(TRIT_P, TRIT_P, &carry);
    ASSERT_EQ(result, TRIT_N);
    ASSERT_EQ(carry, TRIT_P);
}

TEST(test_add_negative_overflow) {
    trit carry = TRIT_Z;

    /* -1 + (-1) = -2 → balanced ternary: +1 with carry -1 */
    trit result = trit_add(TRIT_N, TRIT_N, &carry);
    ASSERT_EQ(result, TRIT_P);
    ASSERT_EQ(carry, TRIT_N);
}

TEST(test_add_with_carry_in) {
    trit carry = TRIT_P;  /* carry = 1 */

    /* 1 + 1 + carry(1) = 3 → 0 with carry +1 */
    trit result = trit_add(TRIT_P, TRIT_P, &carry);
    ASSERT_EQ(result, TRIT_Z);
    ASSERT_EQ(carry, TRIT_P);
}

TEST(test_add_with_negative_carry_in) {
    trit carry = TRIT_N;  /* carry = -1 */

    /* -1 + -1 + carry(-1) = -3 → 0 with carry -1 */
    trit result = trit_add(TRIT_N, TRIT_N, &carry);
    ASSERT_EQ(result, TRIT_Z);
    ASSERT_EQ(carry, TRIT_N);
}

/* ---- trit_min / trit_max tests ---- */

TEST(test_min_basic) {
    ASSERT_EQ(trit_min(TRIT_N, TRIT_P), TRIT_N);
    ASSERT_EQ(trit_min(TRIT_P, TRIT_N), TRIT_N);
    ASSERT_EQ(trit_min(TRIT_Z, TRIT_P), TRIT_Z);
    ASSERT_EQ(trit_min(TRIT_N, TRIT_Z), TRIT_N);
}

TEST(test_min_equal) {
    ASSERT_EQ(trit_min(TRIT_P, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_min(TRIT_Z, TRIT_Z), TRIT_Z);
    ASSERT_EQ(trit_min(TRIT_N, TRIT_N), TRIT_N);
}

TEST(test_max_basic) {
    ASSERT_EQ(trit_max(TRIT_N, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_P, TRIT_N), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_Z, TRIT_N), TRIT_Z);
    ASSERT_EQ(trit_max(TRIT_Z, TRIT_P), TRIT_P);
}

TEST(test_max_equal) {
    ASSERT_EQ(trit_max(TRIT_P, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_Z, TRIT_Z), TRIT_Z);
    ASSERT_EQ(trit_max(TRIT_N, TRIT_N), TRIT_N);
}

/* ---- Full trit_add truth table ---- */

TEST(test_add_exhaustive) {
    /* Test all 9 input combinations (a, b) with carry=0 */
    trit vals[] = {TRIT_N, TRIT_Z, TRIT_P};
    int expected_result[] = {
        /* a=-1,b=-1 */ 1,  /* a=-1,b=0 */ -1, /* a=-1,b=1 */ 0,
        /* a=0, b=-1 */-1,  /* a=0, b=0 */  0, /* a=0, b=1 */ 1,
        /* a=1, b=-1 */ 0,  /* a=1, b=0 */  1, /* a=1, b=1 */-1
    };
    int expected_carry[] = {
        /* a=-1,b=-1 */-1,  /* a=-1,b=0 */  0, /* a=-1,b=1 */ 0,
        /* a=0, b=-1 */ 0,  /* a=0, b=0 */  0, /* a=0, b=1 */ 0,
        /* a=1, b=-1 */ 0,  /* a=1, b=0 */  0, /* a=1, b=1 */ 1
    };

    int idx = 0;
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            trit carry = TRIT_Z;
            trit result = trit_add(vals[i], vals[j], &carry);
            ASSERT_EQ(result, expected_result[idx]);
            ASSERT_EQ(carry, expected_carry[idx]);
            idx++;
        }
    }
}

/* ---- Trit word operations (TASK-002) ---- */

TEST(test_int_to_trit_word_basic) {
    trit_word w;
    int_to_trit_word(0, w);
    ASSERT_EQ(trit_word_to_int(w), 0);

    int_to_trit_word(1, w);
    ASSERT_EQ(trit_word_to_int(w), 1);

    int_to_trit_word(-1, w);
    ASSERT_EQ(trit_word_to_int(w), -1);

    int_to_trit_word(13, w);
    ASSERT_EQ(trit_word_to_int(w), 13);
}

TEST(test_trit_word_add_simple) {
    trit_word a, b, res;
    int_to_trit_word(2, a);
    int_to_trit_word(3, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 5);
}

TEST(test_trit_word_add_carry) {
    trit_word a, b, res;
    int_to_trit_word(100, a);
    int_to_trit_word(200, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 300);
}

TEST(test_trit_word_mul_simple) {
    trit_word a, b, res;
    int_to_trit_word(4, a);
    int_to_trit_word(3, b);
    trit_word_mul(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 12);
}

TEST(test_trit_word_mul_negative) {
    trit_word a, b, res;
    int_to_trit_word(-3, a);
    int_to_trit_word(7, b);
    trit_word_mul(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), -21);
}

TEST(test_trit_word_roundtrip) {
    trit_word w;
    int vals[] = {0, 1, -1, 13, -13, 42, -42, 100, -100, 9841, -9841};
    for (int i = 0; i < 11; i++) {
        int_to_trit_word(vals[i], w);
        ASSERT_EQ(trit_word_to_int(w), vals[i]);
    }
}

int main(void) {
    TEST_SUITE_BEGIN("Trit Operations");

    RUN_TEST(test_mul_pos_pos);
    RUN_TEST(test_mul_pos_neg);
    RUN_TEST(test_mul_neg_neg);
    RUN_TEST(test_mul_zero_any);
    RUN_TEST(test_mul_neg_pos);
    RUN_TEST(test_add_no_carry_basic);
    RUN_TEST(test_add_cancel);
    RUN_TEST(test_add_positive_overflow);
    RUN_TEST(test_add_negative_overflow);
    RUN_TEST(test_add_with_carry_in);
    RUN_TEST(test_add_with_negative_carry_in);
    RUN_TEST(test_min_basic);
    RUN_TEST(test_min_equal);
    RUN_TEST(test_max_basic);
    RUN_TEST(test_max_equal);
    RUN_TEST(test_add_exhaustive);
    RUN_TEST(test_int_to_trit_word_basic);
    RUN_TEST(test_trit_word_add_simple);
    RUN_TEST(test_trit_word_add_carry);
    RUN_TEST(test_trit_word_mul_simple);
    RUN_TEST(test_trit_word_mul_negative);
    RUN_TEST(test_trit_word_roundtrip);

    TEST_SUITE_END();
}
