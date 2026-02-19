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

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) \
    do { printf("  %-55s ", #name); fflush(stdout); } while(0)

#define PASS() \
    do { printf("[PASS]\n"); tests_passed++; } while(0)

#define FAIL(msg) \
    do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

#define ASSERT_EQ(a, b, msg) \
    do { if ((a) != (b)) { FAIL(msg); return; } } while(0)

#define ASSERT_TRUE(cond, msg) \
    do { if (!(cond)) { FAIL(msg); return; } } while(0)

/* ════════════════════════════════════════════════════════════
 * NULL Operation Tests (STRICT, PROPAGATE, LENIENT modes)
 * ════════════════════════════════════════════════════════════ */

void test_null_and_strict(void) {
    TEST(null_and_strict_mode);
    ASSERT_EQ(ternary_null_and(TRIT_TRUE, TRIT_TRUE, TERNARY_NULL_STRICT), TRIT_TRUE, "T AND T = T");
    ASSERT_EQ(ternary_null_and(TRIT_FALSE, TRIT_TRUE, TERNARY_NULL_STRICT), TRIT_FALSE, "F AND T = F");
    ASSERT_EQ(ternary_null_and(TERNARY_NULL, TRIT_TRUE, TERNARY_NULL_STRICT), TERNARY_NULL, "NULL AND T = NULL");
    ASSERT_EQ(ternary_null_and(TRIT_UNKNOWN, TRIT_TRUE, TERNARY_NULL_STRICT), TERNARY_NULL, "U AND T = NULL strict");
    /* STRICT mode: NULL propagates even when binary logic would short-circuit */
    ASSERT_EQ(ternary_null_and(TRIT_FALSE, TERNARY_NULL, TERNARY_NULL_STRICT), TERNARY_NULL, "F AND NULL = NULL (strict propagates)");
    PASS();
}

void test_null_and_propagate(void) {
    TEST(null_and_propagate_mode);
    ASSERT_EQ(ternary_null_and(TRIT_TRUE, TRIT_TRUE, TERNARY_NULL_PROPAGATE), TRIT_TRUE, "T AND T prop");
    ASSERT_EQ(ternary_null_and(TRIT_FALSE, TRIT_TRUE, TERNARY_NULL_PROPAGATE), TRIT_FALSE, "F AND T prop");
    ASSERT_EQ(ternary_null_and(TERNARY_NULL, TRIT_TRUE, TERNARY_NULL_PROPAGATE), TERNARY_NULL, "NULL AND T prop");
    PASS();
}

void test_null_and_lenient(void) {
    TEST(null_and_lenient_mode);
    ASSERT_EQ(ternary_null_and(TRIT_TRUE, TRIT_TRUE, TERNARY_NULL_LENIENT), TRIT_TRUE, "T AND T lenient");
    ASSERT_EQ(ternary_null_and(TRIT_FALSE, TRIT_TRUE, TERNARY_NULL_LENIENT), TRIT_FALSE, "F AND T lenient");
    PASS();
}

void test_null_or_strict(void) {
    TEST(null_or_strict_mode);
    ASSERT_EQ(ternary_null_or(TRIT_FALSE, TRIT_FALSE, TERNARY_NULL_STRICT), TRIT_FALSE, "F OR F = F");
    ASSERT_EQ(ternary_null_or(TRIT_TRUE, TRIT_FALSE, TERNARY_NULL_STRICT), TRIT_TRUE, "T OR F = T");
    ASSERT_EQ(ternary_null_or(TERNARY_NULL, TRIT_FALSE, TERNARY_NULL_STRICT), TERNARY_NULL, "NULL OR F = NULL");
    /* STRICT mode: NULL propagates even when binary logic would short-circuit */
    ASSERT_EQ(ternary_null_or(TRIT_TRUE, TERNARY_NULL, TERNARY_NULL_STRICT), TERNARY_NULL, "T OR NULL = NULL (strict propagates)");
    PASS();
}

void test_null_or_propagate(void) {
    TEST(null_or_propagate_mode);
    ASSERT_EQ(ternary_null_or(TRIT_TRUE, TRIT_FALSE, TERNARY_NULL_PROPAGATE), TRIT_TRUE, "T OR F prop");
    ASSERT_EQ(ternary_null_or(TERNARY_NULL, TRIT_FALSE, TERNARY_NULL_PROPAGATE), TERNARY_NULL, "NULL OR F prop");
    PASS();
}

void test_null_or_lenient(void) {
    TEST(null_or_lenient_mode);
    ASSERT_EQ(ternary_null_or(TRIT_TRUE, TRIT_FALSE, TERNARY_NULL_LENIENT), TRIT_TRUE, "T OR F lenient");
    ASSERT_EQ(ternary_null_or(TRIT_FALSE, TRIT_FALSE, TERNARY_NULL_LENIENT), TRIT_FALSE, "F OR F lenient");
    PASS();
}

void test_null_equals(void) {
    TEST(null_equals_all_combos);
    ASSERT_EQ(ternary_null_equals(TRIT_TRUE, TRIT_TRUE), TRIT_TRUE, "T == T");
    ASSERT_EQ(ternary_null_equals(TRIT_TRUE, TRIT_FALSE), TRIT_FALSE, "T == F is F");
    ASSERT_EQ(ternary_null_equals(TRIT_FALSE, TRIT_FALSE), TRIT_TRUE, "F == F");
    ASSERT_EQ(ternary_null_equals(TERNARY_NULL, TRIT_TRUE), TERNARY_NULL, "NULL == T is NULL");
    ASSERT_EQ(ternary_null_equals(TERNARY_NULL, TERNARY_NULL), TERNARY_NULL, "NULL == NULL is NULL");
    ASSERT_EQ(ternary_null_equals(TRIT_TRUE, TERNARY_NULL), TERNARY_NULL, "T == NULL is NULL");
    PASS();
}

void test_null_count(void) {
    TEST(null_count_aggregation);
    trit vals1[] = {TRIT_TRUE, TRIT_FALSE, TERNARY_NULL, TRIT_TRUE};
    trit c = ternary_null_count(vals1, 4);
    /* 3 non-NULL → positive → TRUE */
    ASSERT_EQ(c, TRIT_TRUE, "count 3 non-null → TRUE");

    trit vals2[] = {TERNARY_NULL, TERNARY_NULL, TERNARY_NULL};
    c = ternary_null_count(vals2, 3);
    /* 0 non-NULL → UNKNOWN */
    ASSERT_EQ(c, TRIT_UNKNOWN, "count 0 non-null → UNKNOWN");
    PASS();
}

void test_null_sum(void) {
    TEST(null_sum_aggregation);
    trit vals[] = {TRIT_TRUE, TRIT_FALSE, TERNARY_NULL, TRIT_TRUE};
    trit s = ternary_null_sum(vals, 4);
    /* +1 + (-1) + skip + (+1) = +1 → TRUE */
    ASSERT_EQ(s, TRIT_TRUE, "sum +1-1+skip+1 → TRUE");

    trit vals2[] = {TRIT_TRUE, TRIT_FALSE};
    s = ternary_null_sum(vals2, 2);
    /* +1 + (-1) = 0 → UNKNOWN */
    ASSERT_EQ(s, TRIT_UNKNOWN, "sum +1-1 → UNKNOWN");
    PASS();
}

void test_null_and_commutativity(void) {
    TEST(null_and_commutativity);
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            trit ab = ternary_null_and(vals[i], vals[j], TERNARY_NULL_STRICT);
            trit ba = ternary_null_and(vals[j], vals[i], TERNARY_NULL_STRICT);
            ASSERT_EQ(ab, ba, "AND commutative");
        }
    }
    PASS();
}

void test_null_or_commutativity(void) {
    TEST(null_or_commutativity);
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) {
            trit ab = ternary_null_or(vals[i], vals[j], TERNARY_NULL_STRICT);
            trit ba = ternary_null_or(vals[j], vals[i], TERNARY_NULL_STRICT);
            ASSERT_EQ(ab, ba, "OR commutative");
        }
    }
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * TCAM (Content-Addressable Memory) Tests
 * ════════════════════════════════════════════════════════════ */

void test_cam_init(void) {
    TEST(cam_init);
    ternary_cam_t cam;
    ternary_cam_init(&cam);
    ASSERT_EQ(cam.num_entries, 0, "init num_entries=0");
    PASS();
}

void test_cam_add_and_search(void) {
    TEST(cam_add_and_search);

    ternary_cam_t cam;
    ternary_cam_init(&cam);

    trit key1[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit data1[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit mask1[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};

    trit key2[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit data2[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};

    ASSERT_EQ(ternary_cam_add(&cam, key1, data1, mask1), 0, "add key1");
    ASSERT_EQ(ternary_cam_add(&cam, key2, data2, NULL), 0, "add key2");

    trit search_key[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    trit result[TCAM_NUM_ENTRIES * TCAM_ENTRY_SIZE];
    int hits = ternary_cam_search(&cam, search_key, result, 10);
    ASSERT_EQ(hits, 1, "search key1 with don't-care");

    trit search_key2[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    hits = ternary_cam_search(&cam, search_key2, result, 10);
    ASSERT_EQ(hits, 1, "search key2 exact");
    PASS();
}

void test_cam_delete(void) {
    TEST(cam_delete_and_verify);

    ternary_cam_t cam;
    ternary_cam_init(&cam);

    trit key1[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit data1[TCAM_ENTRY_SIZE] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    trit mask1[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};
    ternary_cam_add(&cam, key1, data1, mask1);

    ASSERT_EQ(ternary_cam_delete(&cam, key1), 0, "delete key1");
    trit search_key[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    trit result[TCAM_NUM_ENTRIES * TCAM_ENTRY_SIZE];
    int hits = ternary_cam_search(&cam, search_key, result, 10);
    ASSERT_EQ(hits, 0, "key1 deleted");
    PASS();
}

void test_cam_delete_nonexistent(void) {
    TEST(cam_delete_nonexistent);
    ternary_cam_t cam;
    ternary_cam_init(&cam);

    trit key[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    ASSERT_EQ(ternary_cam_delete(&cam, key), -1, "delete from empty = -1");
    PASS();
}

void test_cam_multiple_matches(void) {
    TEST(cam_multiple_matches);
    ternary_cam_t cam;
    ternary_cam_init(&cam);

    /* Add 3 entries that all match a wildcard search */
    trit key1[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    trit key2[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    trit key3[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    trit data1[TCAM_ENTRY_SIZE] = {TRIT_FALSE};
    trit data2[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    trit data3[TCAM_ENTRY_SIZE] = {TRIT_UNKNOWN};

    ternary_cam_add(&cam, key1, data1, NULL);
    ternary_cam_add(&cam, key2, data2, NULL);
    ternary_cam_add(&cam, key3, data3, NULL);

    trit search[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    trit result[TCAM_NUM_ENTRIES * TCAM_ENTRY_SIZE];
    int hits = ternary_cam_search(&cam, search, result, 10);
    ASSERT_TRUE(hits >= 3, "3+ matches found");
    PASS();
}

void test_cam_search_empty(void) {
    TEST(cam_search_empty_table);
    ternary_cam_t cam;
    ternary_cam_init(&cam);

    trit search[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    trit result[TCAM_NUM_ENTRIES * TCAM_ENTRY_SIZE];
    int hits = ternary_cam_search(&cam, search, result, 10);
    ASSERT_EQ(hits, 0, "empty table → 0 hits");
    PASS();
}

void test_cam_null_mask_default(void) {
    TEST(cam_null_mask_defaults_to_all_care);
    ternary_cam_t cam;
    ternary_cam_init(&cam);

    trit key[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE};
    trit data[TCAM_ENTRY_SIZE] = {TRIT_TRUE};
    ternary_cam_add(&cam, key, data, NULL); /* NULL mask → all-care */

    /* Exact match required */
    trit search[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_FALSE};
    trit result[TCAM_NUM_ENTRIES * TCAM_ENTRY_SIZE];
    int hits = ternary_cam_search(&cam, search, result, 10);
    ASSERT_EQ(hits, 1, "exact match with default mask");

    /* Different key → no match */
    trit search2[TCAM_ENTRY_SIZE] = {TRIT_TRUE, TRIT_TRUE};
    hits = ternary_cam_search(&cam, search2, result, 10);
    ASSERT_EQ(hits, 0, "no match with different key");
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Compression Tests (RLE + Huffman)
 * ════════════════════════════════════════════════════════════ */

void test_rle_basic(void) {
    TEST(rle_basic_compress_decompress);

    trit test_data[] = {
        TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE, TRIT_FALSE,
        TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN,
        TRIT_TRUE, TRIT_FALSE
    };
    int data_size = sizeof(test_data) / sizeof(trit);

    trit_rle_compressed_t *compressed = ternary_rle_compress(test_data, data_size);
    ASSERT_TRUE(compressed != NULL, "RLE compress non-null");
    ASSERT_EQ(compressed->num_runs, 5, "RLE 5 runs");

    int decompressed_size;
    trit *decompressed = ternary_rle_decompress(compressed, &decompressed_size);
    ASSERT_TRUE(decompressed != NULL, "RLE decompress non-null");
    ASSERT_EQ(decompressed_size, data_size, "RLE roundtrip size");
    ASSERT_TRUE(memcmp(decompressed, test_data, data_size * sizeof(trit)) == 0, "RLE roundtrip data");

    ternary_rle_free(compressed);
    free(decompressed);
    PASS();
}

void test_rle_single_element(void) {
    TEST(rle_single_element);
    trit data[] = {TRIT_TRUE};
    trit_rle_compressed_t *c = ternary_rle_compress(data, 1);
    ASSERT_TRUE(c != NULL, "single RLE non-null");
    ASSERT_EQ(c->num_runs, 1, "single element → 1 run");

    int sz;
    trit *d = ternary_rle_decompress(c, &sz);
    ASSERT_EQ(sz, 1, "single decompress size=1");
    ASSERT_EQ(d[0], TRIT_TRUE, "single value preserved");

    ternary_rle_free(c);
    free(d);
    PASS();
}

void test_rle_alternating(void) {
    TEST(rle_alternating_pattern);
    trit data[] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    int sz = 5;
    trit_rle_compressed_t *c = ternary_rle_compress(data, sz);
    ASSERT_TRUE(c != NULL, "alternating RLE non-null");
    ASSERT_EQ(c->num_runs, 5, "alternating → 5 runs (worst case)");

    int dsz;
    trit *d = ternary_rle_decompress(c, &dsz);
    ASSERT_EQ(dsz, sz, "alternating roundtrip size");
    ASSERT_TRUE(memcmp(d, data, sz * sizeof(trit)) == 0, "alternating data match");

    ternary_rle_free(c);
    free(d);
    PASS();
}

void test_rle_uniform(void) {
    TEST(rle_uniform_data);
    trit data[100];
    for (int i = 0; i < 100; i++) data[i] = TRIT_UNKNOWN;

    trit_rle_compressed_t *c = ternary_rle_compress(data, 100);
    ASSERT_TRUE(c != NULL, "uniform RLE non-null");
    ASSERT_EQ(c->num_runs, 1, "uniform → 1 run");

    int dsz;
    trit *d = ternary_rle_decompress(c, &dsz);
    ASSERT_EQ(dsz, 100, "uniform roundtrip size=100");

    ternary_rle_free(c);
    free(d);
    PASS();
}

void test_huffman_basic(void) {
    TEST(huffman_basic_compress);
    trit test_data[] = {
        TRIT_TRUE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE, TRIT_FALSE,
        TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN,
        TRIT_TRUE, TRIT_FALSE
    };
    int data_size = sizeof(test_data) / sizeof(trit);

    trit_huffman_tree_t tree;
    ternary_huffman_build(&tree, test_data, data_size);

    int compressed_size;
    uint8_t *compressed = ternary_huffman_compress(&tree, test_data, data_size,
                                                    &compressed_size);
    ASSERT_TRUE(compressed != NULL, "Huffman compress non-null");
    ASSERT_TRUE(compressed_size > 0, "Huffman compressed_size > 0");
    free(compressed);
    PASS();
}

void test_huffman_all_same(void) {
    TEST(huffman_all_same_value);
    trit data[20];
    for (int i = 0; i < 20; i++) data[i] = TRIT_TRUE;

    trit_huffman_tree_t tree;
    ternary_huffman_build(&tree, data, 20);

    int csz;
    uint8_t *c = ternary_huffman_compress(&tree, data, 20, &csz);
    ASSERT_TRUE(c != NULL, "all-same Huffman non-null");
    ASSERT_TRUE(csz > 0, "all-same compressed_size > 0");
    free(c);
    PASS();
}

void test_huffman_three_distinct(void) {
    TEST(huffman_three_distinct_values);
    trit data[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};

    trit_huffman_tree_t tree;
    ternary_huffman_build(&tree, data, 3);

    /* Tree should have entries for all 3 symbols */
    int csz;
    uint8_t *c = ternary_huffman_compress(&tree, data, 3, &csz);
    ASSERT_TRUE(c != NULL, "3-distinct Huffman non-null");
    ASSERT_TRUE(csz > 0, "3-distinct compressed > 0");
    free(c);
    PASS();
}

/* ════════════════════════════════════════════════════════════
 * Database Operations Tests
 * ════════════════════════════════════════════════════════════ */

void test_db_init(void) {
    TEST(db_init);
    ternary_database_t db;
    ternary_db_init(&db, 4, TERNARY_NULL_STRICT);
    ASSERT_EQ(db.num_cols, 4, "num_cols=4");
    ASSERT_EQ(db.num_rows, 0, "num_rows=0");
    ASSERT_EQ(db.null_mode, TERNARY_NULL_STRICT, "null_mode=STRICT");
    PASS();
}

void test_db_insert_and_select(void) {
    TEST(db_insert_and_select);

    ternary_database_t db;
    ternary_db_init(&db, 3, TERNARY_NULL_STRICT);

    trit row1[] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    trit nulls1[] = {TRIT_FALSE, TRIT_FALSE, TRIT_TRUE};

    trit row2[] = {TRIT_FALSE, TRIT_TRUE, TRIT_TRUE};
    trit nulls2[] = {TRIT_FALSE, TRIT_FALSE, TRIT_FALSE};

    ASSERT_EQ(ternary_db_insert(&db, row1, nulls1), 0, "insert row1");
    ASSERT_EQ(ternary_db_insert(&db, row2, nulls2), 0, "insert row2");

    trit *results[TERNARY_DB_MAX_ROWS];
    int num_results = ternary_db_select_where(&db, 0, TRIT_TRUE, results);
    ASSERT_EQ(num_results, 1, "select col0=TRUE");
    ASSERT_EQ(results[0][0], TRIT_TRUE, "result[0][0]=TRUE");

    num_results = ternary_db_select_where(&db, 2, TRIT_TRUE, results);
    ASSERT_EQ(num_results, 1, "select col2=TRUE skips NULL");
    PASS();
}

void test_db_insert_no_nulls(void) {
    TEST(db_insert_no_null_indicators);
    ternary_database_t db;
    ternary_db_init(&db, 2, TERNARY_NULL_PROPAGATE);

    trit row[] = {TRIT_TRUE, TRIT_FALSE};
    ASSERT_EQ(ternary_db_insert(&db, row, NULL), 0, "insert with NULL indicators=NULL");

    trit *results[TERNARY_DB_MAX_ROWS];
    int n = ternary_db_select_where(&db, 0, TRIT_TRUE, results);
    ASSERT_EQ(n, 1, "select finds row");
    PASS();
}

void test_db_empty_select(void) {
    TEST(db_empty_select);
    ternary_database_t db;
    ternary_db_init(&db, 2, TERNARY_NULL_STRICT);

    trit *results[TERNARY_DB_MAX_ROWS];
    int n = ternary_db_select_where(&db, 0, TRIT_TRUE, results);
    ASSERT_EQ(n, 0, "empty db → 0 results");
    PASS();
}

void test_db_multiple_rows(void) {
    TEST(db_multiple_rows_select);
    ternary_database_t db;
    ternary_db_init(&db, 2, TERNARY_NULL_STRICT);

    trit r1[] = {TRIT_TRUE, TRIT_FALSE};
    trit r2[] = {TRIT_FALSE, TRIT_TRUE};
    trit r3[] = {TRIT_TRUE, TRIT_TRUE};
    trit r4[] = {TRIT_UNKNOWN, TRIT_FALSE};
    trit r5[] = {TRIT_TRUE, TRIT_UNKNOWN};

    ternary_db_insert(&db, r1, NULL);
    ternary_db_insert(&db, r2, NULL);
    ternary_db_insert(&db, r3, NULL);
    ternary_db_insert(&db, r4, NULL);
    ternary_db_insert(&db, r5, NULL);

    trit *results[TERNARY_DB_MAX_ROWS];
    int n = ternary_db_select_where(&db, 0, TRIT_TRUE, results);
    ASSERT_EQ(n, 3, "3 rows with col0=TRUE");
    PASS();
}

void test_db_null_mode_propagate(void) {
    TEST(db_null_mode_propagate);
    ternary_database_t db;
    ternary_db_init(&db, 2, TERNARY_NULL_PROPAGATE);

    trit row[] = {TRIT_TRUE, TRIT_FALSE};
    trit nulls[] = {TRIT_TRUE, TRIT_FALSE}; /* col0 is NULL */
    ternary_db_insert(&db, row, nulls);

    trit *results[TERNARY_DB_MAX_ROWS];
    int n = ternary_db_select_where(&db, 0, TRIT_TRUE, results);
    /* With NULL propagation, NULL column should not match */
    ASSERT_EQ(n, 0, "NULL col0 doesn't match in propagate mode");
    PASS();
}

void test_db_select_false_value(void) {
    TEST(db_select_false_value);
    ternary_database_t db;
    ternary_db_init(&db, 2, TERNARY_NULL_STRICT);

    trit r1[] = {TRIT_FALSE, TRIT_TRUE};
    trit r2[] = {TRIT_TRUE, TRIT_FALSE};
    ternary_db_insert(&db, r1, NULL);
    ternary_db_insert(&db, r2, NULL);

    trit *results[TERNARY_DB_MAX_ROWS];
    int n = ternary_db_select_where(&db, 0, TRIT_FALSE, results);
    ASSERT_EQ(n, 1, "1 row with col0=FALSE");
    ASSERT_EQ(results[0][1], TRIT_TRUE, "correct row returned");
    PASS();
}

int main(void) {
    printf("=== Ternary Database and Storage Layer Test Suite ===\n\n");

    printf("[NULL Operations — Strict]\n");
    test_null_and_strict();
    test_null_or_strict();

    printf("\n[NULL Operations — Propagate]\n");
    test_null_and_propagate();
    test_null_or_propagate();

    printf("\n[NULL Operations — Lenient]\n");
    test_null_and_lenient();
    test_null_or_lenient();

    printf("\n[NULL Operations — Equality & Aggregate]\n");
    test_null_equals();
    test_null_count();
    test_null_sum();

    printf("\n[NULL Operations — Algebraic Properties]\n");
    test_null_and_commutativity();
    test_null_or_commutativity();

    printf("\n[TCAM Operations]\n");
    test_cam_init();
    test_cam_add_and_search();
    test_cam_delete();
    test_cam_delete_nonexistent();
    test_cam_multiple_matches();
    test_cam_search_empty();
    test_cam_null_mask_default();

    printf("\n[RLE Compression]\n");
    test_rle_basic();
    test_rle_single_element();
    test_rle_alternating();
    test_rle_uniform();

    printf("\n[Huffman Compression]\n");
    test_huffman_basic();
    test_huffman_all_same();
    test_huffman_three_distinct();

    printf("\n[Database Operations]\n");
    test_db_init();
    test_db_insert_and_select();
    test_db_insert_no_nulls();
    test_db_empty_select();
    test_db_multiple_rows();
    test_db_null_mode_propagate();
    test_db_select_false_value();

    printf("\n=== Results: %d passed, %d failed ===\n", tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}