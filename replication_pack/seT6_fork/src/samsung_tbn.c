/**
 * @file samsung_tbn.c
 * @brief TBN Inference Engine for Samsung US11170290B2 NAND Chip
 *
 * Implements the ternary-binary neural network dot-product computation,
 * matrix-vector multiplication, Zero Input Detection (ZID), and
 * multi-layer DNN inference described in Samsung patent US11170290B2.
 *
 * Software emulation path:
 *   1. Encodes inputs as voltage patterns (WL pairs)
 *   2. Programs weights as unit synapses (SLC cell pairs)
 *   3. Evaluates each synapse (series conductivity test)
 *   4. Accumulates conducting synapses via counter
 *   5. Applies ZID correction for zero inputs
 *   6. Corrects dot-product: P = 2·CNT − (S − Z)
 *
 * MMIO hardware path (when real silicon is present):
 *   1. Writes input vector to SS_REG_INPUT_VEC registers
 *   2. Issues SS_CMD_COMPUTE_DOT / SS_CMD_COMPUTE_ROW command
 *   3. Reads corrected result from SS_REG_DOT_PRODUCT
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/samsung_tbn.h"
#include <string.h>
#include <stdlib.h>

/* ===================================================================== */
/* Internal: Emulated Dot-Product Core                                   */
/* ===================================================================== */

/**
 * Core dot-product computation using unit synapse emulation.
 *
 * For each position i in [0, size):
 *   1. Program a unit synapse with weights[i]
 *   2. Encode inputs[i] as a voltage pattern
 *   3. Evaluate synapse conductivity (XNOR of input/weight)
 *   4. If ZID detects zero input, exclude from counter
 *   5. Otherwise, increment counter if synapse conducts
 *
 * Then apply correction formula:
 *   BNN: P = 2·CNT − S
 *   TBN: P = 2·CNT − (S − Z)
 */
static ss_dot_result_t ss_dot_emulated(const ss_weight_t *weights,
                                        const ss_input_t *inputs,
                                        int size,
                                        int use_zid)
{
    ss_dot_result_t result;
    result.s_total = size;
    result.cnt_out = 0;
    result.z_count = 0;

    for (int i = 0; i < size; i++) {
        /* Program synapse with weight */
        ss_unit_synapse_t syn = ss_synapse_program(weights[i]);

        /* Encode input as voltage pattern */
        ss_voltage_pattern_t vp = ss_encode_input(inputs[i]);

        /* ZID: detect zero input */
        if (use_zid && ss_is_zero_input(vp)) {
            result.z_count++;
            /* Zero input: skip this synapse in the counter (BCC active) */
            continue;
        }

        /* Evaluate synapse: does the NAND string conduct? */
        if (ss_synapse_eval(syn, vp)) {
            result.cnt_out++;
        }
    }

    /* Compute corrected dot-product */
    result.s_effective = result.s_total - result.z_count;
    result.dot_product = 2 * result.cnt_out - result.s_effective;

    return result;
}

/* ===================================================================== */
/* Public: Dot-Product Functions                                         */
/* ===================================================================== */

ss_dot_result_t ss_dot_bnn(const ss_hal_state_t *state,
                            const ss_weight_t *weights,
                            const ss_input_t *inputs,
                            int size)
{
    (void)state;  /* Mode validation would happen here on real HW */

    /* BNN: no ZID needed (no zero inputs expected) */
    return ss_dot_emulated(weights, inputs, size, 0);
}

ss_dot_result_t ss_dot_tbn(const ss_hal_state_t *state,
                            const ss_weight_t *weights,
                            const ss_input_t *inputs,
                            int size)
{
    int use_zid = (state && state->zid_enabled) ? 1 : 1;
    /* TBN always uses ZID to handle zero inputs correctly */
    (void)use_zid;

    return ss_dot_emulated(weights, inputs, size, 1);
}

ss_dot_result_t ss_dot_auto(const ss_hal_state_t *state,
                             const ss_weight_t *weights,
                             const ss_input_t *inputs,
                             int size)
{
    if (state && state->net_mode == SS_MODE_BNN)
        return ss_dot_bnn(state, weights, inputs, size);
    return ss_dot_tbn(state, weights, inputs, size);
}

/* ===================================================================== */
/* Public: Zero Input Detection                                          */
/* ===================================================================== */

int ss_zid_count_zeros(const ss_input_t *inputs, int size)
{
    int z = 0;
    for (int i = 0; i < size; i++) {
        /* ZID NOR gate: both word lines at Vread ↔ input == 0 */
        ss_voltage_pattern_t vp = ss_encode_input(inputs[i]);
        if (ss_is_zero_input(vp))
            z++;
    }
    return z;
}

void ss_zid_bitmap(const ss_input_t *inputs, int size, uint32_t *bitmap)
{
    int num_words = (size + 31) / 32;
    memset(bitmap, 0, (size_t)num_words * sizeof(uint32_t));

    for (int i = 0; i < size; i++) {
        if (inputs[i] == SS_INPUT_ZERO) {
            bitmap[i / 32] |= (1u << (i % 32));
        }
    }
}

/* ===================================================================== */
/* Public: Matrix-Vector Multiplication                                  */
/* ===================================================================== */

int ss_matmul(const ss_hal_state_t *state,
              const ss_weight_t *weights,
              const ss_input_t *inputs,
              int rows, int cols,
              int *outputs)
{
    if (!state || !state->initialized || !weights || !inputs || !outputs)
        return -1;
    if (rows <= 0 || cols <= 0)
        return -1;

    /*
     * Each row of the weight matrix maps to one NAND string (bit line).
     * The input vector is applied to all strings simultaneously via
     * word-line voltage patterns.
     *
     * On hardware, all rows are computed in parallel by the sense
     * amplifiers. In emulation, we iterate sequentially.
     */
    for (int r = 0; r < rows; r++) {
        const ss_weight_t *row_weights = &weights[r * cols];
        ss_dot_result_t dot;

        if (state->net_mode == SS_MODE_TBN) {
            dot = ss_dot_tbn(state, row_weights, inputs, cols);
        } else {
            dot = ss_dot_bnn(state, row_weights, inputs, cols);
        }

        outputs[r] = dot.dot_product;
    }

    return 0;
}

/* ===================================================================== */
/* Public: Weight Programming                                            */
/* ===================================================================== */

/*
 * In-memory weight storage model.
 *
 * For emulation, we don't have real NAND cells.  The caller provides
 * weight arrays directly to dot-product/matmul functions.
 * These functions serve as the interface for real hardware, where
 * weights must be physically programmed into the NAND array.
 */

int ss_program_weights(ss_hal_state_t *state,
                       const ss_weight_t *weights,
                       int rows, int cols,
                       int block_id)
{
    if (!state || !state->initialized || !weights)
        return -1;
    if (rows <= 0 || cols <= 0 || block_id < 0)
        return -1;

    if (state->mode == SS_MODE_MMIO && state->mmio_base) {
        /* Hardware path: program weights via MMIO registers */
        for (int r = 0; r < rows; r++) {
            for (int c = 0; c < cols; c++) {
                uint32_t prog = 0;
                prog |= ((uint32_t)block_id & 0xFF);
                prog |= ((uint32_t)(r & 0xFF)) << 8;
                prog |= ((uint32_t)(c & 0xFF)) << 16;
                prog |= (weights[r * cols + c] == SS_WEIGHT_POS)
                         ? (1u << 24) : 0;
                prog |= (1u << 31);  /* Write trigger */
                ss_mmio_write(state->mmio_base, SS_REG_WEIGHT_PROG, prog);
            }
        }
        return 0;
    }

    /* Emulated: weights are passed directly, nothing to store */
    (void)block_id;
    return 0;
}

int ss_read_weights(const ss_hal_state_t *state,
                    ss_weight_t *weights,
                    int rows, int cols,
                    int block_id)
{
    if (!state || !state->initialized || !weights)
        return -1;
    if (rows <= 0 || cols <= 0 || block_id < 0)
        return -1;

    /* Emulated: return all-positive placeholder (real HW would read cells) */
    (void)block_id;
    for (int i = 0; i < rows * cols; i++) {
        weights[i] = SS_WEIGHT_POS;
    }

    return 0;
}

/* ===================================================================== */
/* Public: Multi-Layer DNN Inference                                     */
/* ===================================================================== */

int ss_dnn_inference(const ss_hal_state_t *state,
                     const ss_dnn_config_t *config,
                     const ss_input_t *input, int input_size,
                     int *output, int output_size,
                     int threshold)
{
    if (!state || !state->initialized || !config || !input || !output)
        return -1;
    if (config->num_layers <= 0)
        return -1;

    /*
     * Working buffers for inter-layer data flow.
     * We alternate between two buffers to avoid extra copies.
     */
    int max_size = input_size;
    for (int l = 0; l < config->num_layers; l++) {
        if (config->layers[l].rows > max_size)
            max_size = config->layers[l].rows;
        if (config->layers[l].cols > max_size)
            max_size = config->layers[l].cols;
    }

    int *dot_buf = (int *)calloc((size_t)max_size, sizeof(int));
    ss_input_t *act_buf = (ss_input_t *)calloc((size_t)max_size,
                                                sizeof(ss_input_t));
    if (!dot_buf || !act_buf) {
        free(dot_buf);
        free(act_buf);
        return -1;
    }

    /* Copy initial input */
    const ss_input_t *current_input = input;
    int current_size = input_size;

    for (int l = 0; l < config->num_layers; l++) {
        const ss_layer_config_t *layer = &config->layers[l];

        /* Validate dimensions */
        if (layer->cols != current_size) {
            free(dot_buf);
            free(act_buf);
            return -1;
        }

        /* Matrix-vector multiply: y = W · x */
        int rc = ss_matmul(state, layer->weights, current_input,
                           layer->rows, layer->cols, dot_buf);
        if (rc != 0) {
            free(dot_buf);
            free(act_buf);
            return -1;
        }

        /* Apply activation function */
        for (int i = 0; i < layer->rows; i++) {
            if (threshold > 0) {
                act_buf[i] = ss_activation_ternary(dot_buf[i], threshold);
            } else {
                act_buf[i] = ss_activation_sign(dot_buf[i]);
            }
        }

        /* Activated output becomes input for next layer */
        current_input = act_buf;
        current_size = layer->rows;
    }

    /* Copy final layer dot-products to output */
    int copy_size = (current_size < output_size) ? current_size : output_size;
    for (int i = 0; i < copy_size; i++) {
        output[i] = dot_buf[i];
    }

    free(dot_buf);
    free(act_buf);
    return 0;
}
