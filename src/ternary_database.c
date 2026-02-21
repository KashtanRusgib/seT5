/**
 * @file ternary_database.c
 * @brief seT6 Ternary Database and Storage Layer
 *
 * Implements ternary NULL handling in Trit Linux, content-addressable memory
 * integration, and ternary compression algorithms for efficient storage.
 *
 * Key Components:
 * - Ternary NULL propagation (UNKNOWN represents NULL)
 * - Content-addressable memory (CAM) operations using Hynix TCAM
 * - Ternary compression with run-length encoding and trit packing
 * - Database query operations with ternary logic filters
 * - Storage of ternary arrays and objects
 *
 * Data Structures:
 * - ternary_record_t: Structure for database records with ternary fields
 * - ternary_filter_t: Filter objects for ternary queries
 * - compressed_trit_array_t: Compressed ternary data storage
 *
 * Functions:
 * - ternary_null_propagate: Apply NULL propagation rules
 * - ternary_compress: Compress ternary data using RLE
 * - ternary_decompress: Decompress ternary data
 * - ternary_query: Execute queries with ternary filters
 * - cam_search: Content-addressable search in TCAM
 * - ternary_store: Store ternary records with compression
 *
 * Purpose: Provide a database layer optimized for ternary data, handling NULL
 * values with ternary logic, enabling efficient storage and querying of
 * ternary information in seT6 systems.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include "set5/hynix_tcam.h"
#include <stdint.h>
#include <string.h>
#include <stdlib.h>

/* ---- Helper functions ---- */

/**
 * Simple trit addition without carry (for basic arithmetic)
 */
static trit trit_add_simple(trit a, trit b) {
    trit carry = TRIT_UNKNOWN;
    int sum = (int)a + (int)b + (int)carry;
    if (sum > 1) {
        return (trit)(sum - 3);
    } else if (sum < -1) {
        return (trit)(sum + 3);
    } else {
        return (trit)sum;
    }
}

/**
 * Convert small integer to trit (for counts)
 */
static trit int_to_trit(int val) {
    if (val == 0) return TRIT_UNKNOWN;
    if (val > 0) return TRIT_TRUE;
    return TRIT_FALSE;
}

/* ---- Ternary NULL Handling (SQL-like) ---- */

#define TERNARY_NULL TRIT_UNKNOWN  // Unknown represents NULL in ternary logic
#define TERNARY_TRUE_FILTER TRIT_TRUE
#define TERNARY_FALSE_FILTER TRIT_FALSE

typedef enum {
    TERNARY_NULL_PROPAGATE,    // NULL propagates through operations
    TERNARY_NULL_STRICT,       // Operations with NULL return NULL
    TERNARY_NULL_LENIENT       // Some operations ignore NULL
} ternary_null_mode_t;

/**
 * Ternary NULL-aware logical operations
 * Similar to SQL three-valued logic
 */
trit ternary_null_and(trit a, trit b, ternary_null_mode_t mode) {
    if (mode == TERNARY_NULL_STRICT) {
        if (a == TERNARY_NULL || b == TERNARY_NULL) {
            return TERNARY_NULL;
        }
    }

    // Standard Kleene AND with NULL propagation
    if (a == TRIT_FALSE || b == TRIT_FALSE) {
        return TRIT_FALSE;
    }
    if (a == TRIT_TRUE && b == TRIT_TRUE) {
        return TRIT_TRUE;
    }
    return TERNARY_NULL;  // Either NULL or mixed TRUE/NULL
}

trit ternary_null_or(trit a, trit b, ternary_null_mode_t mode) {
    if (mode == TERNARY_NULL_STRICT) {
        if (a == TERNARY_NULL || b == TERNARY_NULL) {
            return TERNARY_NULL;
        }
    }

    // Standard Kleene OR with NULL propagation
    if (a == TRIT_TRUE || b == TRIT_TRUE) {
        return TRIT_TRUE;
    }
    if (a == TRIT_FALSE && b == TRIT_FALSE) {
        return TRIT_FALSE;
    }
    return TERNARY_NULL;  // Either NULL or mixed FALSE/NULL
}

/**
 * Ternary NULL-safe equality comparison
 */
trit ternary_null_equals(trit a, trit b) {
    if (a == TERNARY_NULL || b == TERNARY_NULL) {
        return TERNARY_NULL;  // NULL = anything -> NULL
    }
    return (a == b) ? TRIT_TRUE : TRIT_FALSE;
}

/**
 * Ternary NULL aggregation functions
 */
trit ternary_null_count(const trit *values, int count) {
    int non_null_count = 0;
    for (int i = 0; i < count; i++) {
        if (values[i] != TERNARY_NULL) {
            non_null_count++;
        }
    }
    // Return count as ternary-encoded integer
    return int_to_trit(non_null_count);
}

trit ternary_null_sum(const trit *values, int count) {
    trit sum = TRIT_UNKNOWN;  // 0 in ternary
    for (int i = 0; i < count; i++) {
        if (values[i] != TERNARY_NULL) {
            sum = trit_add_simple(sum, values[i]);
        }
        // If any NULL encountered, result depends on mode
        // For now, NULLs are ignored in sum
    }
    return sum;
}

/* ---- Content-Addressable Memory Integration ---- */

#define TCAM_ENTRY_SIZE 64
#define TCAM_NUM_ENTRIES 1024

typedef struct {
    trit key[TCAM_ENTRY_SIZE];      // Search key
    trit data[TCAM_ENTRY_SIZE];     // Associated data
    trit mask[TCAM_ENTRY_SIZE];     // Don't care mask
    trit valid;                     // Entry valid flag
} ternary_cam_entry_t;

typedef struct {
    ternary_cam_entry_t entries[TCAM_NUM_ENTRIES];
    int num_entries;
    trit search_result[TCAM_NUM_ENTRIES];  // Hit vector
} ternary_cam_t;

/**
 * Initialize ternary CAM
 */
void ternary_cam_init(ternary_cam_t *cam) {
    memset(cam, 0, sizeof(*cam));
    cam->num_entries = 0;
}

/**
 * Add entry to ternary CAM
 */
int ternary_cam_add(ternary_cam_t *cam, const trit *key, const trit *data,
                   const trit *mask) {
    if (cam->num_entries >= TCAM_NUM_ENTRIES) {
        return -1;  // CAM full
    }

    ternary_cam_entry_t *entry = &cam->entries[cam->num_entries];
    memcpy(entry->key, key, TCAM_ENTRY_SIZE * sizeof(trit));
    memcpy(entry->data, data, TCAM_ENTRY_SIZE * sizeof(trit));
    if (mask) {
        memcpy(entry->mask, mask, TCAM_ENTRY_SIZE * sizeof(trit));
    } else {
        // Default: all bits matter
        memset(entry->mask, TRIT_TRUE, TCAM_ENTRY_SIZE * sizeof(trit));
    }
    entry->valid = TRIT_TRUE;

    cam->num_entries++;
    return 0;
}

/**
 * Search ternary CAM
 */
int ternary_cam_search(const ternary_cam_t *cam, const trit *search_key,
                      trit *result_data, int max_results) {
    int hits = 0;

    for (int i = 0; i < cam->num_entries; i++) {
        const ternary_cam_entry_t *entry = &cam->entries[i];
        if (entry->valid != TRIT_TRUE) continue;

        // Perform ternary match with don't cares
        trit match = TRIT_TRUE;
        for (int j = 0; j < TCAM_ENTRY_SIZE; j++) {
            if (entry->mask[j] == TRIT_TRUE) {  // Bit matters
                if (search_key[j] != entry->key[j]) {
                    match = TRIT_FALSE;
                    break;
                }
            }
            // If mask[j] is FALSE or UNKNOWN, bit is don't care
        }

        if (match == TRIT_TRUE) {
            if (hits < max_results) {
                memcpy(&result_data[hits * TCAM_ENTRY_SIZE],
                       entry->data, TCAM_ENTRY_SIZE * sizeof(trit));
            }
            hits++;
        }
    }

    return hits;
}

/**
 * Delete entry from ternary CAM
 */
int ternary_cam_delete(ternary_cam_t *cam, const trit *key) {
    for (int i = 0; i < cam->num_entries; i++) {
        ternary_cam_entry_t *entry = &cam->entries[i];
        if (entry->valid == TRIT_TRUE) {
            // Check if keys match
            trit match = TRIT_TRUE;
            for (int j = 0; j < TCAM_ENTRY_SIZE; j++) {
                if (key[j] != entry->key[j]) {
                    match = TRIT_FALSE;
                    break;
                }
            }

            if (match == TRIT_TRUE) {
                entry->valid = TRIT_FALSE;
                return 0;  // Success
            }
        }
    }
    return -1;  // Not found
}

/* ---- Ternary Compression Algorithms ---- */

#define TRIT_RUN_LENGTH_MAX 255

typedef struct {
    trit value;     // Run value
    uint8_t length; // Run length
} trit_run_t;

typedef struct {
    trit_run_t *runs;
    int num_runs;
    int original_size;
} trit_rle_compressed_t;

/**
 * Ternary Run-Length Encoding (RLE) compression
 */
trit_rle_compressed_t *ternary_rle_compress(const trit *data, int size) {
    if (size <= 0) return NULL;

    trit_rle_compressed_t *compressed = malloc(sizeof(trit_rle_compressed_t));
    if (!compressed) return NULL;

    // Allocate maximum possible runs
    compressed->runs = malloc(size * sizeof(trit_run_t));
    if (!compressed->runs) {
        free(compressed);
        return NULL;
    }

    compressed->num_runs = 0;
    compressed->original_size = size;

    trit current_value = data[0];
    uint8_t current_length = 1;

    for (int i = 1; i < size; i++) {
        if (data[i] == current_value && current_length < TRIT_RUN_LENGTH_MAX) {
            current_length++;
        } else {
            // Save current run
            compressed->runs[compressed->num_runs].value = current_value;
            compressed->runs[compressed->num_runs].length = current_length;
            compressed->num_runs++;

            // Start new run
            current_value = data[i];
            current_length = 1;
        }
    }

    // Save final run
    compressed->runs[compressed->num_runs].value = current_value;
    compressed->runs[compressed->num_runs].length = current_length;
    compressed->num_runs++;

    return compressed;
}

/**
 * Ternary RLE decompression
 */
trit *ternary_rle_decompress(const trit_rle_compressed_t *compressed, int *size) {
    if (!compressed || compressed->num_runs <= 0) return NULL;

    *size = compressed->original_size;
    trit *data = malloc(*size * sizeof(trit));
    if (!data) return NULL;

    int pos = 0;
    for (int i = 0; i < compressed->num_runs; i++) {
        trit value = compressed->runs[i].value;
        uint8_t length = compressed->runs[i].length;

        for (int j = 0; j < length && pos < *size; j++) {
            data[pos++] = value;
        }
    }

    return data;
}

/**
 * Free RLE compressed data
 */
void ternary_rle_free(trit_rle_compressed_t *compressed) {
    if (compressed) {
        free(compressed->runs);
        free(compressed);
    }
}

/**
 * Ternary Huffman coding for entropy-based compression
 */
#define TRIT_HUFFMAN_MAX_CODE_LEN 16

typedef struct {
    trit symbol;
    uint32_t frequency;
    char code[TRIT_HUFFMAN_MAX_CODE_LEN];
    int code_length;
} trit_huffman_entry_t;

typedef struct {
    trit_huffman_entry_t entries[3];  // Three possible symbols
    trit_huffman_entry_t *root;
} trit_huffman_tree_t;

/**
 * Build ternary Huffman tree based on symbol frequencies
 */
void ternary_huffman_build(trit_huffman_tree_t *tree, const trit *data, int size) {
    // Count frequencies
    uint32_t freq[3] = {0, 0, 0};  // FALSE, UNKNOWN, TRUE

    for (int i = 0; i < size; i++) {
        switch (data[i]) {
            case TRIT_FALSE: freq[0]++; break;
            case TRIT_UNKNOWN: freq[1]++; break;
            case TRIT_TRUE: freq[2]++; break;
        }
    }

    // Initialize entries
    tree->entries[0].symbol = TRIT_FALSE;
    tree->entries[0].frequency = freq[0];

    tree->entries[1].symbol = TRIT_UNKNOWN;
    tree->entries[1].frequency = freq[1];

    tree->entries[2].symbol = TRIT_TRUE;
    tree->entries[2].frequency = freq[2];

    // Simple ternary Huffman: assign shortest codes to most frequent
    // Sort by frequency (bubble sort for simplicity)
    for (int i = 0; i < 2; i++) {
        for (int j = 0; j < 2 - i; j++) {
            if (tree->entries[j].frequency < tree->entries[j + 1].frequency) {
                trit_huffman_entry_t temp = tree->entries[j];
                tree->entries[j] = tree->entries[j + 1];
                tree->entries[j + 1] = temp;
            }
        }
    }

    // Assign Huffman codes (T-028: base-3 trit codes — native ternary)
    // Three symbols map naturally to 3 single-trit codes:
    //   Most frequent  → "T" (trit +1, code_length 1)
    //   Second         → "0" (trit  0, code_length 1)
    //   Least frequent → "F" (trit -1, code_length 1)
    // This achieves optimal 1-trit-per-symbol encoding for a 3-symbol
    // alphabet, giving exactly log_3(3) = 1 trit per symbol.
    strcpy(tree->entries[0].code, "T");  // Most frequent → +1
    tree->entries[0].code_length = 1;

    strcpy(tree->entries[1].code, "0"); // Second most frequent → 0
    tree->entries[1].code_length = 1;

    strcpy(tree->entries[2].code, "F"); // Least frequent → -1
    tree->entries[2].code_length = 1;
}

/**
 * Compress data using ternary Huffman coding
 */
uint8_t *ternary_huffman_compress(const trit_huffman_tree_t *tree,
                                 const trit *data, int size, int *compressed_size) {
    // Calculate compressed size
    *compressed_size = 0;
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < 3; j++) {
            if (data[i] == tree->entries[j].symbol) {
                *compressed_size += tree->entries[j].code_length;
                break;
            }
        }
    }

    // Allocate compressed buffer (bits to bytes)
    int byte_size = (*compressed_size + 7) / 8;
    uint8_t *compressed = calloc(byte_size, sizeof(uint8_t));
    if (!compressed) return NULL;

    // Encode data
    int bit_pos = 0;
    for (int i = 0; i < size; i++) {
        for (int j = 0; j < 3; j++) {
            if (data[i] == tree->entries[j].symbol) {
                const char *code = tree->entries[j].code;
                int code_len = tree->entries[j].code_length;

                for (int k = 0; k < code_len; k++) {
                    if (code[k] == '1') {
                        compressed[bit_pos / 8] |= (1 << (7 - (bit_pos % 8)));
                    }
                    bit_pos++;
                }
                break;
            }
        }
    }

    return compressed;
}

/* ---- Ternary Database Operations ---- */

#define TERNARY_DB_MAX_ROWS 1000
#define TERNARY_DB_MAX_COLS 16

typedef struct {
    trit data[TERNARY_DB_MAX_ROWS][TERNARY_DB_MAX_COLS];
    trit null_mask[TERNARY_DB_MAX_ROWS][TERNARY_DB_MAX_COLS];  // NULL indicators
    int num_rows;
    int num_cols;
    ternary_null_mode_t null_mode;
} ternary_database_t;

/**
 * Initialize ternary database
 */
void ternary_db_init(ternary_database_t *db, int num_cols, ternary_null_mode_t null_mode) {
    memset(db, 0, sizeof(*db));
    /* VULN-66 fix: clamp num_cols to prevent stack overflow in data arrays */
    db->num_cols = (num_cols > 0 && num_cols <= TERNARY_DB_MAX_COLS) ? num_cols : TERNARY_DB_MAX_COLS;
    db->null_mode = null_mode;
}

/**
 * Insert row with ternary NULL handling
 */
int ternary_db_insert(ternary_database_t *db, const trit *row_data,
                     const trit *null_indicators) {
    if (db->num_rows >= TERNARY_DB_MAX_ROWS) {
        return -1;  // Database full
    }

    memcpy(db->data[db->num_rows], row_data, db->num_cols * sizeof(trit));
    if (null_indicators) {
        memcpy(db->null_mask[db->num_rows], null_indicators, db->num_cols * sizeof(trit));
    } else {
        // No NULLs specified
        memset(db->null_mask[db->num_rows], TRIT_FALSE, db->num_cols * sizeof(trit));
    }

    db->num_rows++;
    return 0;
}

/**
 * Query with ternary NULL-aware conditions
 */
int ternary_db_select_where(ternary_database_t *db, int col_idx, trit condition_value,
                           trit *result_rows[TERNARY_DB_MAX_ROWS]) {
    int result_count = 0;

    /* VULN-65 fix: bounds check col_idx to prevent OOB read */
    if (!db || col_idx < 0 || col_idx >= db->num_cols) return 0;

    for (int row = 0; row < db->num_rows; row++) {
        trit cell_value = db->data[row][col_idx];
        trit is_null = db->null_mask[row][col_idx];

        // Apply NULL-aware comparison
        trit matches = TRIT_FALSE;

        if (is_null == TRIT_TRUE) {
            // NULL handling based on mode
            if (db->null_mode == TERNARY_NULL_LENIENT) {
                matches = TRIT_UNKNOWN;  // Maybe matches
            }
        } else {
            matches = ternary_null_equals(cell_value, condition_value);
        }

        if (matches == TRIT_TRUE) {
            result_rows[result_count++] = db->data[row];
        }
    }

    return result_count;
}