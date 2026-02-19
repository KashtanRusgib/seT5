/**
 * @file test_samsung_cn105745888a_correlator.c
 * @brief Test suite for Samsung correlator hardware
 *
 * Tests ternary sequence correlation
 * as implemented in hw/samsung_cn105745888a_correlator.v
 *
 * Build: gcc -Wall -Wextra -Iinclude -o test_samsung_cn105745888a_correlator \
 *        tests/test_samsung_cn105745888a_correlator.c src/samsung_cn105745888a_correlator.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>

#include "set5/samsung_cn105745888a_correlator.h"

/* Test harness */
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) printf("  %-50s ", #name); fflush(stdout);
#define PASS() do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)
#define ASSERT_EQ(a, b) if ((a) != (b)) { FAIL("expected " #b); return; }

/* Identical sequences */
static void test_correlate_identical(void) {
    TEST(correlate_identical);
    uint8_t seq1[4] = {1, 2, 0, 1};  // +1, -1, 0, +1
    uint8_t seq2[4] = {1, 2, 0, 1};
    int16_t result = samsung_correlate(seq1, seq2, 4);
    ASSERT_EQ(result, 1 + 1 + 0 + 1);  // 3
    PASS();
}

/* Orthogonal sequences */
static void test_correlate_orthogonal(void) {
    TEST(correlate_orthogonal);
    uint8_t seq1[4] = {1, 1, 1, 1};  // +1 +1 +1 +1
    uint8_t seq2[4] = {2, 2, 2, 2};  // -1 -1 -1 -1
    int16_t result = samsung_correlate(seq1, seq2, 4);
    ASSERT_EQ(result, -4);
    PASS();
}

/* Main */
int main(void) {
    printf("=== Samsung Correlator Test Suite ===\n\n");

    test_correlate_identical();
    test_correlate_orthogonal();

    printf("\nTotal: %d, Passed: %d, Failed: %d\n",
           tests_passed + tests_failed, tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}