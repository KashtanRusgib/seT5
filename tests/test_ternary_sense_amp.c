/**
 * @file test_ternary_sense_amp.c
 * @brief Test suite for ternary sense amplifier hardware
 *
 * Tests current sensing and trit output
 * as implemented in hw/ternary_sense_amp.v
 *
 * Build: gcc -Wall -Wextra -Iinclude -o test_ternary_sense_amp \
 *        tests/test_ternary_sense_amp.c src/ternary_sense_amp.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>

#include "set5/ternary_sense_amp.h"

/* Test harness */
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) printf("  %-50s ", #name); fflush(stdout);
#define PASS() do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)
#define ASSERT_EQ(a, b) if ((a) != (b)) { FAIL("expected " #b); return; }

/* Low current */
static void test_sense_low(void) {
    TEST(sense_low);
    uint8_t result = ternary_sense_amp_read(5);
    ASSERT_EQ(result, 0);
    PASS();
}

/* Mid current */
static void test_sense_mid(void) {
    TEST(sense_mid);
    uint8_t result = ternary_sense_amp_read(30);
    ASSERT_EQ(result, 1);
    PASS();
}

/* High current */
static void test_sense_high(void) {
    TEST(sense_high);
    uint8_t result = ternary_sense_amp_read(60);
    ASSERT_EQ(result, 2);
    PASS();
}

/* Main */
int main(void) {
    printf("=== Ternary Sense Amp Test Suite ===\n\n");

    test_sense_low();
    test_sense_mid();
    test_sense_high();

    printf("\nTotal: %d, Passed: %d, Failed: %d\n",
           tests_passed + tests_failed, tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}