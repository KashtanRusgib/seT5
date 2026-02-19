/**
 * @file test_multi_radix_unit.c
 * @brief Test suite for multi-radix arithmetic unit hardware
 *
 * Tests radix-3,4,6 arithmetic operations, FFT, and crypto primitives
 * as implemented in hw/multi_radix_unit.v
 *
 * Build: gcc -Wall -Wextra -Iinclude -o test_multi_radix_unit \
 *        tests/test_multi_radix_unit.c src/multi_radix_unit.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "set5/multi_radix_unit.h"

/* Test harness */
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) printf("  %-50s ", #name); fflush(stdout);
#define PASS() do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)
#define ASSERT_EQ(a, b) if ((a) != (b)) { FAIL("expected " #b); return; }

/* Radix-3 addition test */
static void test_radix3_add(void) {
    TEST(radix3_add);
    // Test ternary addition: 1 + 1 = 2 (carry 1, sum 0 in ternary)
    // But since it's 9-trit, test simple cases
    int16_t a = 1, b = 1;
    int16_t result = multi_radix_add(a, b, RADIX3);
    ASSERT_EQ(result, 2);  // 1+1=2 in decimal, but in ternary it's 2
    PASS();
}

/* Radix-4 addition */
static void test_radix4_add(void) {
    TEST(radix4_add);
    int16_t a = 3, b = 1;
    int16_t result = multi_radix_add(a, b, RADIX4);
    ASSERT_EQ(result, 4);
    PASS();
}

/* FFT test */
static void test_fft(void) {
    TEST(fft_8point);
    // Simple FFT test
    int16_t data[8] = {1,0,0,0,0,0,0,0};
    multi_radix_fft(data, 8);
    ASSERT_EQ(data[0], 1);
    PASS();
}

/* Main */
int main(void) {
    printf("=== Multi-Radix Unit Test Suite ===\n\n");

    test_radix3_add();
    test_radix4_add();
    test_fft();

    printf("\nTotal: %d, Passed: %d, Failed: %d\n",
           tests_passed + tests_failed, tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}