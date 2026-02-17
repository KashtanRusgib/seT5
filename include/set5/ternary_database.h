/**
 * @file ternary_database.h
 * @brief seT6 Ternary Database and Storage Layer Header
 *
 * Header definitions for ternary NULL handling, content-addressable memory,
 * and compression algorithms.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TERNARY_DATABASE_H
#define TERNARY_DATABASE_H

#include "set5/trit.h"
#include <stdint.h>

/* ---- Ternary NULL Handling ---- */

#define TERNARY_NULL TRIT_UNKNOWN

typedef enum {
    TERNARY_NULL_PROPAGATE,
    TERNARY_NULL_STRICT,
    TERNARY_NULL_LENIENT
} ternary_null_mode_t;

trit ternary_null_and(trit a, trit b, ternary_null_mode_t mode);
trit ternary_null_or(trit a, trit b, ternary_null_mode_t mode);
trit ternary_null_equals(trit a, trit b);
trit ternary_null_count(const trit *values, int count);
trit ternary_null_sum(const trit *values, int count);

/* ---- Content-Addressable Memory ---- */

#define TCAM_ENTRY_SIZE 64
#define TCAM_NUM_ENTRIES 1024

typedef struct {
    trit key[TCAM_ENTRY_SIZE];
    trit data[TCAM_ENTRY_SIZE];
    trit mask[TCAM_ENTRY_SIZE];
    trit valid;
} ternary_cam_entry_t;

typedef struct {
    ternary_cam_entry_t entries[TCAM_NUM_ENTRIES];
    int num_entries;
    trit search_result[TCAM_NUM_ENTRIES];
} ternary_cam_t;

void ternary_cam_init(ternary_cam_t *cam);
int ternary_cam_add(ternary_cam_t *cam, const trit *key, const trit *data,
                   const trit *mask);
int ternary_cam_search(const ternary_cam_t *cam, const trit *search_key,
                      trit *result_data, int max_results);
int ternary_cam_delete(ternary_cam_t *cam, const trit *key);

/* ---- Ternary Compression ---- */

#define TRIT_RUN_LENGTH_MAX 255

typedef struct {
    trit value;
    uint8_t length;
} trit_run_t;

typedef struct {
    trit_run_t *runs;
    int num_runs;
    int original_size;
} trit_rle_compressed_t;

trit_rle_compressed_t *ternary_rle_compress(const trit *data, int size);
trit *ternary_rle_decompress(const trit_rle_compressed_t *compressed, int *size);
void ternary_rle_free(trit_rle_compressed_t *compressed);

#define TRIT_HUFFMAN_MAX_CODE_LEN 16

typedef struct {
    trit symbol;
    uint32_t frequency;
    char code[TRIT_HUFFMAN_MAX_CODE_LEN];
    int code_length;
} trit_huffman_entry_t;

typedef struct {
    trit_huffman_entry_t entries[3];
    trit_huffman_entry_t *root;
} trit_huffman_tree_t;

void ternary_huffman_build(trit_huffman_tree_t *tree, const trit *data, int size);
uint8_t *ternary_huffman_compress(const trit_huffman_tree_t *tree,
                                 const trit *data, int size, int *compressed_size);

/* ---- Ternary Database Operations ---- */

#define TERNARY_DB_MAX_ROWS 1000
#define TERNARY_DB_MAX_COLS 16

typedef struct {
    trit data[TERNARY_DB_MAX_ROWS][TERNARY_DB_MAX_COLS];
    trit null_mask[TERNARY_DB_MAX_ROWS][TERNARY_DB_MAX_COLS];
    int num_rows;
    int num_cols;
    ternary_null_mode_t null_mode;
} ternary_database_t;

void ternary_db_init(ternary_database_t *db, int num_cols, ternary_null_mode_t null_mode);
int ternary_db_insert(ternary_database_t *db, const trit *row_data,
                     const trit *null_indicators);
int ternary_db_select_where(ternary_database_t *db, int col_idx, trit condition_value,
                           trit *result_rows[TERNARY_DB_MAX_ROWS]);

#endif /* TERNARY_DATABASE_H */