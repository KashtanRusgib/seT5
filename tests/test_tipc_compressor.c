/**
 * @file test_tipc_compressor.c
 * @brief Test suite for T-IPC compressor hardware
 *
 * Tests compression and decompression of trit streams
 * as implemented in hw/tipc_compressor.v
 *
 * Build: gcc -Wall -Wextra -Iinclude -o test_tipc_compressor \
 *        tests/test_tipc_compressor.c src/tipc_compressor.c
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "set5/tipc_compressor.h"

/* Test harness */
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) printf("  %-50s ", #name); fflush(stdout);
#define PASS() do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg) do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)
#define ASSERT_EQ(a, b) if ((a) != (b)) { FAIL("expected " #b); return; }

/* Round-trip test */
static void test_compress_decompress(void) {
    TEST(compress_decompress);
    uint8_t trits[9] = {0, 1, 2, 0, 1, 2, 0, 1, 2};
    uint8_t compressed[3] = {0};  // enough for 18 bits
    int bit_count = tipc_compress(trits, compressed, 3);
    ASSERT_EQ(bit_count, 15);  // 1+2+2+1+2+2+1+2+2 = 15

    uint8_t decompressed[9];
    int decompressed_count = tipc_decompress(compressed, bit_count, decompressed);
    ASSERT_EQ(decompressed_count, 9);
    for (int i = 0; i < 9; i++) {
        ASSERT_EQ(decompressed[i], trits[i]);
    }
    PASS();
}

/* All zeros */
static void test_all_zeros(void) {
    TEST(all_zeros);
    uint8_t trits[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0};
    uint8_t compressed[2] = {0};
    int bit_count = tipc_compress(trits, compressed, 2);
    ASSERT_EQ(bit_count, 9);

    uint8_t decompressed[9];
    tipc_decompress(compressed, bit_count, decompressed);
    for (int i = 0; i < 9; i++) {
        ASSERT_EQ(decompressed[i], 0);
    }
    PASS();
}

/* Main */
int main(void) {
    printf("=== T-IPC Compressor Test Suite ===\n\n");

    test_compress_decompress();
    test_all_zeros();

    printf("\nTotal: %d, Passed: %d, Failed: %d\n",
           tests_passed + tests_failed, tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}