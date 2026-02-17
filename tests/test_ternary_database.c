/**
 * @file test_ternary_database.c
 * @brief Test suite for seT6 Ternary Database and Storage Layer
 *
 * Tests ternary NULL handling, TCAM operations, compression algorithms,
 * and database queries.
 */

#include "set5/ternary_database.h"
#include "set5/trit.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

void test_ternary_null_operations() {
    printf("Testing ternary NULL operations...\n");

    // Test NULL AND operations
    assert(ternary_null_and(TRIT_TRUE, TRIT_TRUE, TERNARY_NULL_STRICT) == TRIT_TRUE);
    assert(ternary_null_and(TRIT_FALSE, TRIT_TRUE, TERNARY_NULL_STRICT) == TRIT_FALSE);
    assert(ternary_null_and(TERNARY_NULL, TRIT_TRUE, TERNARY_NULL_STRICT) == TERNARY_NULL);
    assert(ternary_null_and(TRIT_UNKNOWN, TRIT_TRUE, TERNARY_NULL_STRICT) == TERNARY_NULL);

    // Test NULL OR operations
    assert(ternary_null_or(TRIT_FALSE, TRIT_FALSE, TERNARY_NULL_STRICT) == TRIT_FALSE);
    assert(ternary_null_or(TRIT_TRUE, TRIT_FALSE, TERNARY_NULL_STRICT) == TRIT_TRUE);
    assert(ternary_null_or(TERNARY_NULL, TRIT_FALSE, TERNARY_NULL_STRICT) == TERNARY_NULL);

    // Test NULL equality
    assert(ternary_null_equals(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE);
    assert(ternary_null_equals(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE);
    assert(ternary_null_equals(TERNARY_NULL, TRIT_TRUE) == TERNARY_NULL);
    assert(ternary_null_equals(TERNARY_NULL, TERNARY_NULL) == TERNARY_NULL);

    printf("✓ Ternary NULL operations passed\n");
}

void test_ternary_cam() {
    printf("Testing ternary CAM operations...\n");

    ternary_cam_t cam;
    ternary_cam_init(&cam);

    // Test data
    trit key1[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit data1[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit mask1[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};  // Third bit don't care

    trit key2[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit data2[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};

    // Add entries
    assert(ternary_cam_add(&cam, key1, data1, mask1) == 0);
    assert(ternary_cam_add(&cam, key2, data2, NULL) == 0);

    // Search for exact match
    trit search_key[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    trit result[TCAM_NUM_ENTRIES * TCAM_ENTRY_SIZE];
    int hits = ternary_cam_search(&cam, search_key, result, 10);

    assert(hits == 1);  // Should match key1 (third bit is don't care)

    // Search for second entry
    trit search_key2[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    hits = ternary_cam_search(&cam, search_key2, result, 10);
    assert(hits == 1);

    // Delete entry
    assert(ternary_cam_delete(&cam, key1) == 0);
    hits = ternary_cam_search(&cam, search_key, result, 10);
    assert(hits == 0);  // Should be gone

    printf("✓ Ternary CAM operations passed\n");
}

void test_ternary_compression() {
    printf("Testing ternary compression algorithms...\n");

    // Test data with runs
    trit test_data[] = {
        TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE, TRIT_FALSE,
        TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN,
        TRIT_TRUE, TRIT_FALSE
    };
    int data_size = sizeof(test_data) / sizeof(trit);

    // Test RLE compression
    trit_rle_compressed_t *compressed = ternary_rle_compress(test_data, data_size);
    assert(compressed != NULL);
    assert(compressed->num_runs == 5);  // TRUE(3), FALSE(2), UNKNOWN(4), TRUE(1), FALSE(1)

    // Test decompression
    int decompressed_size;
    trit *decompressed = ternary_rle_decompress(compressed, &decompressed_size);
    assert(decompressed != NULL);
    assert(decompressed_size == data_size);
    assert(memcmp(decompressed, test_data, data_size * sizeof(trit)) == 0);

    ternary_rle_free(compressed);
    free(decompressed);

    // Test Huffman coding
    trit_huffman_tree_t huffman_tree;
    ternary_huffman_build(&huffman_tree, test_data, data_size);

    int compressed_size;
    uint8_t *huffman_compressed = ternary_huffman_compress(&huffman_tree,
                                                          test_data, data_size,
                                                          &compressed_size);
    assert(huffman_compressed != NULL);
    assert(compressed_size > 0);

    free(huffman_compressed);

    printf("✓ Ternary compression algorithms passed\n");
}

void test_ternary_database() {
    printf("Testing ternary database operations...\n");

    ternary_database_t db;
    ternary_db_init(&db, 3, TERNARY_NULL_STRICT);

    // Insert rows with NULLs
    trit row1[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit nulls1[] = {TRIT_FALSE, TRIT_FALSE, TRIT_TRUE};  // Third column is NULL

    trit row2[] = {TRIT_FALSE, TRIT_TRUE, TRIT_TRUE};
    trit nulls2[] = {TRIT_FALSE, TRIT_FALSE, TRIT_FALSE};  // No NULLs

    assert(ternary_db_insert(&db, row1, nulls1) == 0);
    assert(ternary_db_insert(&db, row2, nulls2) == 0);

    // Query for rows where column 0 is TRUE
    trit *results[TERNARY_DB_MAX_ROWS];
    int num_results = ternary_db_select_where(&db, 0, TRIT_TRUE, results);
    assert(num_results == 1);
    assert(results[0][0] == TRIT_TRUE);

    // Query for rows where column 2 is TRUE (should not match NULL)
    num_results = ternary_db_select_where(&db, 2, TRIT_TRUE, results);
    assert(num_results == 1);  // Only row2 matches

    printf("✓ Ternary database operations passed\n");
}

int main() {
    printf("Running seT6 Ternary Database Tests...\n\n");

    test_ternary_null_operations();
    test_ternary_cam();
    test_ternary_compression();
    test_ternary_database();

    printf("\n✅ All ternary database tests passed!\n");
    return 0;
}