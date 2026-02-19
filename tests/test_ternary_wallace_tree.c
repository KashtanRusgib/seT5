/**
 * @file test_ternary_wallace_tree.c
 * @brief Test suite for ternary Wallace tree multiplier hardware
 *
 * Tests ternary multiplication using Wallace tree reduction
 * as implemented in hw/ternary_wallace_tree.v
 *
 * Build: gcc -Wall -Wextra -Iinclude -o test_ternary_wallace_tree \
 *        tests/test_ternary_wallace_tree.c src/ternary_wallace_tree.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>

#include "set5/ternary_wallace_tree.h"

/* Test harness */
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) printf("  %-50s ", #name); fflush(stdout);
#define PASS() do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)
#define ASSERT_EQ(a, b) if ((a) != (b)) { FAIL("expected " #b); return; }

/* Basic multiplication test */
static void test_multiply_basic(void) {
    TEST(multiply_basic);
    int16_t result = ternary_wallace_multiply(2, 3);
    ASSERT_EQ(result, 6);
    PASS();
}

/* Zero multiplication */
static void test_multiply_zero(void) {
    TEST(multiply_zero);
    int16_t result = ternary_wallace_multiply(0, 5);
    ASSERT_EQ(result, 0);
    PASS();
}

/* Main */
int main(void) {
    printf("=== Ternary Wallace Tree Test Suite ===\n\n");

    test_multiply_basic();
    test_multiply_zero();

    printf("\nTotal: %d, Passed: %d, Failed: %d\n",
           tests_passed + tests_failed, tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}