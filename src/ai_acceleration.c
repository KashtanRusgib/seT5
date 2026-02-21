/**
 * @file ai_acceleration.c
 * @brief seT6 AI Acceleration Framework
 *
 * Implements BitNet b1.58 ternary quantization, DLFET-RM ternary gate simulation,
 * and sparse ternary matrix operations for neural network acceleration.
 *
 * Key Components:
 * - Ternary weight quantization with BitNet b1.58 scaling (factor 1000, threshold ratio 0.7)
 * - DLFET-RM gate simulation for ternary logic in neural nets
 * - Sparse matrix operations using ternary values (TRUE, FALSE, UNKNOWN)
 * - Voltage-based trit conversion for analog AI chips
 * - Ternary XOR, multiplication, and addition primitives
 * - Matrix-vector multiplication with ternary weights
 * - Quantization functions for converting float weights to ternary
 *
 * Data Structures:
 * - trit arrays for weights and activations
 * - Voltage thresholds for trit classification
 * - Quantization parameters (scale, threshold)
 *
 * Functions:
 * - trit_to_voltage: Convert trit to analog voltage
 * - voltage_to_trit: Classify voltage to nearest trit
 * - quantize_weights: Apply BitNet quantization to float array
 * - ternary_matmul: Sparse ternary matrix multiplication
 * - simulate_dlfet_rm: DLFET-RM gate logic simulation
 *
 * Purpose: Accelerate AI inference on ternary hardware by providing efficient
 * ternary arithmetic and quantization primitives, enabling low-power neural
 * network execution with ternary weights and activations.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include "set5/ternary_weight_quantizer.h"
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

/* ---- Local helpers ---- */

/** Ternary XOR (symmetric difference) */
static trit trit_xor(trit a, trit b) {
    int s = (int)a + (int)b;
    if (s >  1) s -= 3;
    if (s < -1) s += 3;
    return (trit)s;
}

/** Ternary multiplication */
static trit trit_mul(trit a, trit b) {
    return (trit)((int)a * (int)b);
}

/** Ternary addition (without carry) */
static trit trit_add_simple(trit a, trit b) {
    int s = (int)a + (int)b;
    if (s >  1) s -= 3;
    if (s < -1) s += 3;
    return (trit)s;
}

/* Forward declarations */
static float trit_to_voltage(trit t);
static trit  voltage_to_trit(float voltage);

/* ---- BitNet b1.58 Ternary Quantization ---- */

#define BITNET_SCALE_FACTOR 1000
#define BITNET_THRESHOLD_RATIO 7  // 0.7 ratio

/**
 * Enhanced BitNet b1.58 quantization with ternary optimization
 */
void bitnet_quantize_layer(trit *output_weights, const float *input_weights,
                          int num_weights, float *scale_factor) {
    // Calculate threshold as 0.7 * mean absolute value
    float sum_abs = 0.0f;
    for (int i = 0; i < num_weights; i++) {
        sum_abs += fabsf(input_weights[i]);
    }
    float mean_abs = sum_abs / num_weights;
    float threshold = 0.7f * mean_abs;

    // Find maximum absolute value for scaling
    float max_abs = 0.0f;
    for (int i = 0; i < num_weights; i++) {
        if (fabsf(input_weights[i]) > max_abs) {
            max_abs = fabsf(input_weights[i]);
        }
    }

    // Scale factor to map to ternary range
    *scale_factor = (max_abs > 0.0f) ? (BITNET_SCALE_FACTOR / max_abs) : 1.0f;

    // Quantize to ternary {-1, 0, +1}
    for (int i = 0; i < num_weights; i++) {
        float scaled_weight = input_weights[i] * (*scale_factor);

        if (scaled_weight > threshold) {
            output_weights[i] = TRIT_TRUE;   // +1
        } else if (scaled_weight < -threshold) {
            output_weights[i] = TRIT_FALSE;  // -1
        } else {
            output_weights[i] = TRIT_UNKNOWN; // 0
        }
    }
}

/**
 * BitNet forward pass with ternary operations
 */
void bitnet_forward(const trit *weights, const float *input, float *output,
                   int input_size, int output_size, float scale_factor) {
    for (int out_idx = 0; out_idx < output_size; out_idx++) {
        float sum = 0.0f;
        for (int in_idx = 0; in_idx < input_size; in_idx++) {
            // Ternary multiplication: weight * input
            trit weight = weights[out_idx * input_size + in_idx];
            switch (weight) {
                case TRIT_TRUE:   sum += input[in_idx]; break;
                case TRIT_FALSE:  sum -= input[in_idx]; break;
                case TRIT_UNKNOWN: /* sum += 0 */ break;
            }
        }
        output[out_idx] = sum / scale_factor;
    }
}

/* ---- DLFET-RM Ternary Gate Simulation ---- */

#define DLFET_VDD 1.0f
#define DLFET_THRESHOLD 0.3f

typedef enum {
    DLFET_UNBALANCED,  // 0/1/2 representation
    DLFET_BALANCED     // -1/0/+1 representation
} dlfet_mode_t;

typedef struct {
    float gate_voltage;
    float drain_voltage;
    dlfet_mode_t mode;
} dlfet_gate_t;

/**
 * DLFET-RM ternary NOT gate simulation
 */
trit dlfet_not(trit input) {
    // Simulate ternary inverter using DLFET characteristics
    float v_in = trit_to_voltage(input);
    float v_out = DLFET_VDD - v_in;  // Simple inversion

    // Add threshold behavior
    if (v_out > DLFET_VDD - DLFET_THRESHOLD) {
        return TRIT_TRUE;
    } else if (v_out < DLFET_THRESHOLD) {
        return TRIT_FALSE;
    } else {
        return TRIT_UNKNOWN;
    }
}

/**
 * DLFET-RM ternary NAND gate simulation
 */
trit dlfet_nand(trit a, trit b) {
    // NAND: ~(a & b)
    trit and_result = trit_and(a, b);
    return dlfet_not(and_result);
}

/**
 * DLFET-RM full adder simulation
 */
void dlfet_full_adder(trit a, trit b, trit carry_in,
                     trit *sum, trit *carry_out) {
    // Sum = a ⊕ b ⊕ carry_in (ternary XOR)
    trit xor_ab = trit_xor(a, b);
    *sum = trit_xor(xor_ab, carry_in);

    // Carry = majority function with ternary logic
    // carry = (a & b) | (a & carry_in) | (b & carry_in)
    trit ab_and = trit_and(a, b);
    trit ac_and = trit_and(a, carry_in);
    trit bc_and = trit_and(b, carry_in);

    trit carry_or1 = trit_or(ab_and, ac_and);
    *carry_out = trit_or(carry_or1, bc_and);
}

/**
 * Convert trit to voltage level for DLFET simulation
 */
static float trit_to_voltage(trit t) {
    switch (t) {
        case TRIT_FALSE:  return 0.0f;
        case TRIT_UNKNOWN: return DLFET_VDD / 2.0f;
        case TRIT_TRUE:   return DLFET_VDD;
        default:          return DLFET_VDD / 2.0f;
    }
}

/**
 * Convert voltage to trit for DLFET output
 */
static trit voltage_to_trit(float voltage) {
    if (voltage > DLFET_VDD - DLFET_THRESHOLD) {
        return TRIT_TRUE;
    } else if (voltage < DLFET_THRESHOLD) {
        return TRIT_FALSE;
    } else {
        return TRIT_UNKNOWN;
    }
}

/* ---- Sparse Ternary Matrix Operations ---- */

#define SPARSE_BLOCK_SIZE 4
#define SPARSE_THRESHOLD 2  // Max non-zero elements per block

typedef struct {
    int rows;
    int cols;
    trit *values;           // Non-zero values
    int *row_indices;       // Row indices
    int *col_indices;       // Column indices
    int nnz;               // Number of non-zero elements
    int block_size;        // Block size for N:M sparsity
    int max_nz_per_block;  // Max non-zeros per block
} sparse_trit_matrix_t;

/**
 * Create sparse ternary matrix with N:M structured sparsity
 */
sparse_trit_matrix_t *sparse_trit_matrix_create(int rows, int cols,
                                               int block_size, int max_nz) {
    sparse_trit_matrix_t *matrix = malloc(sizeof(sparse_trit_matrix_t));
    if (!matrix) return NULL;

    matrix->rows = rows;
    matrix->cols = cols;
    matrix->block_size = block_size;
    matrix->max_nz_per_block = max_nz;
    matrix->nnz = 0;

    // Allocate storage for sparse representation
    /* VULN-64 fix: check for integer overflow before allocation.
     * rows * cols * max_nz could overflow int, leading to a tiny
     * malloc followed by massive OOB writes. */
    if (block_size <= 0) { free(matrix); return NULL; }
    long long max_possible_nnz_ll = ((long long)rows * cols * max_nz) / block_size;
    if (max_possible_nnz_ll <= 0 || max_possible_nnz_ll > (1LL << 24)) {
        /* Cap at 16M entries to prevent absurd allocations */
        free(matrix);
        return NULL;
    }
    int max_possible_nnz = (int)max_possible_nnz_ll;
    matrix->values = malloc(max_possible_nnz * sizeof(trit));
    matrix->row_indices = malloc(max_possible_nnz * sizeof(int));
    matrix->col_indices = malloc(max_possible_nnz * sizeof(int));

    if (!matrix->values || !matrix->row_indices || !matrix->col_indices) {
        free(matrix->values);
        free(matrix->row_indices);
        free(matrix->col_indices);
        free(matrix);
        return NULL;
    }

    return matrix;
}

/**
 * Convert dense ternary matrix to sparse with N:M constraints
 */
void dense_to_sparse_trit(const trit *dense, int rows, int cols,
                         sparse_trit_matrix_t *sparse) {
    sparse->nnz = 0;

    for (int block_row = 0; block_row < rows; block_row += sparse->block_size) {
        for (int block_col = 0; block_col < cols; block_col += sparse->block_size) {

            // Count non-zeros in this block
            int nz_count = 0;
            trit block_values[SPARSE_BLOCK_SIZE * SPARSE_BLOCK_SIZE];
            int block_positions[SPARSE_BLOCK_SIZE * SPARSE_BLOCK_SIZE];

            for (int r = 0; r < sparse->block_size; r++) {
                for (int c = 0; c < sparse->block_size; c++) {
                    int row = block_row + r;
                    int col = block_col + c;
                    if (row < rows && col < cols) {
                        trit val = dense[row * cols + col];
                        if (val != TRIT_UNKNOWN) {
                            block_values[nz_count] = val;
                            block_positions[nz_count] = r * sparse->block_size + c;
                            nz_count++;
                        }
                    }
                }
            }

            // Apply N:M sparsity constraint
            if (nz_count > sparse->max_nz_per_block) {
                // Keep only the largest magnitude elements
                // Simple selection: keep first max_nz_per_block
                nz_count = sparse->max_nz_per_block;
            }

            // Store non-zero elements
            for (int i = 0; i < nz_count; i++) {
                if (sparse->nnz < (rows * cols * sparse->max_nz_per_block) / sparse->block_size) {
                    int row = block_row + (block_positions[i] / sparse->block_size);
                    int col = block_col + (block_positions[i] % sparse->block_size);

                    sparse->values[sparse->nnz] = block_values[i];
                    sparse->row_indices[sparse->nnz] = row;
                    sparse->col_indices[sparse->nnz] = col;
                    sparse->nnz++;
                }
            }
        }
    }
}

/**
 * Sparse ternary matrix-vector multiplication
 */
void sparse_trit_mvm(const sparse_trit_matrix_t *matrix, const trit *vector,
                    trit *result) {
    // Initialize result to zero
    memset(result, 0, matrix->rows * sizeof(trit));

    // Perform sparse multiplication
    for (int i = 0; i < matrix->nnz; i++) {
        int row = matrix->row_indices[i];
        int col = matrix->col_indices[i];
        trit weight = matrix->values[i];
        trit input = vector[col];

        // Ternary multiplication and addition
        trit product = trit_mul(weight, input);
        result[row] = trit_add_simple(result[row], product);
    }
}

/**
 * Free sparse ternary matrix
 */
void sparse_trit_matrix_free(sparse_trit_matrix_t *matrix) {
    if (matrix) {
        free(matrix->values);
        free(matrix->row_indices);
        free(matrix->col_indices);
        free(matrix);
    }
}

/* ---- Ternary Neural Network Layers ---- */

typedef struct {
    sparse_trit_matrix_t *weights;
    trit *biases;
    int input_size;
    int output_size;
    float scale_factor;
} ternary_linear_layer_t;

/**
 * Create ternary linear layer with sparse weights
 */
ternary_linear_layer_t *ternary_linear_create(int input_size, int output_size) {
    ternary_linear_layer_t *layer = malloc(sizeof(ternary_linear_layer_t));
    if (!layer) return NULL;

    layer->input_size = input_size;
    layer->output_size = output_size;
    layer->weights = sparse_trit_matrix_create(output_size, input_size,
                                               SPARSE_BLOCK_SIZE, SPARSE_THRESHOLD);
    layer->biases = calloc(output_size, sizeof(trit));

    if (!layer->weights || !layer->biases) {
        sparse_trit_matrix_free(layer->weights);
        free(layer->biases);
        free(layer);
        return NULL;
    }

    return layer;
}

/**
 * Forward pass through ternary linear layer
 */
void ternary_linear_forward(const ternary_linear_layer_t *layer,
                           const trit *input, trit *output) {
    // Sparse matrix-vector multiplication
    sparse_trit_mvm(layer->weights, input, output);

    // Add biases
    for (int i = 0; i < layer->output_size; i++) {
        output[i] = trit_add_simple(output[i], layer->biases[i]);
    }
}

/**
 * Ternary activation function (ReLU-like)
 */
trit ternary_activation(trit x) {
    // Ternary ReLU: negative -> 0, zero -> 0, positive -> positive
    switch (x) {
        case TRIT_FALSE: return TRIT_UNKNOWN;  // -1 -> 0
        case TRIT_UNKNOWN: return TRIT_UNKNOWN; // 0 -> 0
        case TRIT_TRUE: return TRIT_TRUE;      // +1 -> +1
        default: return TRIT_UNKNOWN;
    }
}