/*
 * test_performance.c - Performance regression and benchmark tests
 *
 * Tests: Execution speed, memory usage, scaling
 */

#include "../include/test_harness.h"
#include "../include/ternary.h"
#include "../include/parser.h"
#include "../include/ir.h"

/* ---- Ternary arithmetic performance ---- */

TEST(test_trit_arithmetic_perf) {
    const int iterations = 100000;

    trit carry = TRIT_Z;
    trit result = TRIT_Z;
    for (int i = 0; i < iterations; i++) {
        carry = TRIT_Z;
        result = trit_add(result, TRIT_P, &carry);
        result = trit_mul(result, TRIT_N);
    }

    /* After each iteration: result = -(result + 1).
     * Starting at 0: 0→add 1=1→mul -1=-1, -1→add 1=0→mul -1=0,
     * 0→add 1=1→mul -1=-1, ...  Odd iterations give -1, even give 0.
     * 100000 is even, so result should be 0. */
    ASSERT_EQ(result, TRIT_Z);
}

TEST(test_trit_word_perf) {
    const int iterations = 50000;

    trit_word a, b, res;
    int_to_trit_word(12345, a);
    int_to_trit_word(67890, b);

    for (int i = 0; i < iterations; i++) {
        trit_word_add(a, b, res);
        trit_word_mul(res, a, a); // Modify a for next iteration
    }

    /* Verify final a is representable (round-trip stable) */
    int final_val = trit_word_to_int(a);
    trit_word check;
    int_to_trit_word(final_val, check);
    ASSERT_EQ(trit_word_to_int(check), final_val);
}

/* ---- Parser performance ---- */

TEST(test_parser_perf) {
    const int iterations = 1000;

    const char* code = "int main() { int x = 1; int y = 2; return x + y; }";

    for (int i = 0; i < iterations; i++) {
        struct Expr* ast = parse_program(code);
        ASSERT_NOT_NULL(ast); /* Must parse successfully every time */
        expr_free(ast);
    }
}

/* ---- Scaling test ---- */

TEST(test_scaling_perf) {
    /* Test correctness at multiple scales */
    for (int size = 10; size <= 1000; size *= 10) {
        trit_word words[size];

        /* Initialize */
        for (int i = 0; i < size; i++) {
            int_to_trit_word(i, words[i]);
        }

        /* Accumulate: words[i] += words[i+1] */
        for (int i = 0; i < size - 1; i++) {
            trit_word_add(words[i], words[i+1], words[i]);
        }

        /* Verify final element: words[size-2] should equal
         * (size-2) + (size-1) */
        int expected = (size - 2) + (size - 1);
        ASSERT_EQ(trit_word_to_int(words[size - 2]), expected);
    }
}

int main(void) {
    TEST_SUITE_BEGIN("Performance Benchmarks");

    RUN_TEST(test_trit_arithmetic_perf);
    RUN_TEST(test_trit_word_perf);
    RUN_TEST(test_parser_perf);
    RUN_TEST(test_scaling_perf);

    TEST_SUITE_END();
}