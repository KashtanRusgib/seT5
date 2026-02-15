/**
 * @file samsung_tbn.h
 * @brief TBN (Ternary-Binary Network) Inference Engine Interface
 *
 * High-level interface for neural network inference on the Samsung
 * US11170290B2 NAND in-memory computing chip.
 *
 * Key operations:
 *
 *   1. Dot-product computation:
 *      - BNN: P = 2·CNT_out − S          (Eq. 1 from patent)
 *      - TBN: P = 2·CNT_out − (S − Z)    (Eq. 2 from patent)
 *      Where S = input vector size, Z = # zero inputs, CNT_out =
 *      count of conducting synapses (zero-input positions excluded).
 *
 *   2. Matrix-vector multiply:
 *      Multiple dot-products in parallel (one per output neuron / bit line).
 *      Weight matrix W[M×S] × input vector x[S] → output y[M].
 *
 *   3. Zero Input Detection (ZID):
 *      NOR-gate circuit on word-line pairs detects zero inputs.
 *      Combinational logic generates BCC signal to counter circuit,
 *      excluding zero-input synapse outputs from accumulation.
 *
 *   4. Multi-layer inference (pipelined):
 *      Layer 0 outputs → activation → Layer 1 inputs → ...
 *      Plane pipelining maps layers to different planes/blocks.
 *
 * All functions accept seT5 balanced ternary values {-1, 0, +1}
 * for inputs and {-1, +1} for weights. The HAL handles NAND
 * voltage pattern encoding internally.
 *
 * When real hardware is absent, all operations are computed using
 * cycle-accurate software emulation of the patent circuits.
 *
 * @see samsung_us11170290b2.h — Top-level header, types, unit synapse
 * @see samsung_nand.h         — NAND array model, MMIO registers
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SAMSUNG_TBN_H
#define SET5_SAMSUNG_TBN_H

#include "set5/samsung_us11170290b2.h"
#include "set5/samsung_nand.h"
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Dot-Product Result                                                    */
/* ===================================================================== */

/**
 * @brief Result of a single dot-product computation.
 */
typedef struct {
    int    dot_product;    /**< Corrected dot-product value P */
    int    cnt_out;        /**< Raw count of conducting synapses */
    int    s_total;        /**< Total vector size S */
    int    z_count;        /**< Zero inputs detected (0 for BNN) */
    int    s_effective;    /**< Effective S: S − Z (BNN: S) */
} ss_dot_result_t;

/* ===================================================================== */
/* Matrix-Vector Multiply Result                                         */
/* ===================================================================== */

/**
 * @brief Result of a matrix-vector multiplication W·x.
 *
 * W is M×S (M output neurons, S input synapses per neuron).
 * x is S×1 ternary input vector.
 * y is M×1 output vector.
 */
typedef struct {
    int   *outputs;        /**< Array of M dot-product results (caller allocates) */
    int    num_outputs;    /**< Number of output neurons M */
    int    vector_size;    /**< Input vector size S */
    int    z_count;        /**< Total zero inputs detected */
} ss_matmul_result_t;

/* ===================================================================== */
/* Layer Configuration for Multi-Layer DNN                               */
/* ===================================================================== */

/**
 * @brief Configuration for one DNN layer.
 */
typedef struct {
    const ss_weight_t  *weights;     /**< Weight matrix [rows × cols], row-major */
    int                 rows;        /**< Output dimension (rows / output neurons) */
    int                 cols;        /**< Input dimension (cols / synapses) */
    int                 plane_id;    /**< Plane index for pipelining (-1 = auto) */
    int                 block_id;    /**< Block index (-1 = auto) */
} ss_layer_config_t;

/**
 * @brief Multi-layer DNN configuration.
 */
typedef struct {
    ss_layer_config_t  *layers;      /**< Array of layer configurations */
    int                 num_layers;  /**< Number of layers */
    ss_parallelism_t    par_level;   /**< Parallelism mode */
} ss_dnn_config_t;

/* ===================================================================== */
/* Dot-Product Functions                                                 */
/* ===================================================================== */

/**
 * @brief Compute a single BNN dot-product.
 *
 * Applies BNN formula: P = 2·CNT_out − S  (Eq. 1).
 * Inputs must be binary {-1, +1} only (no zeros).
 *
 * @param state    HAL state (must be initialised, mode = BNN).
 * @param weights  Weight vector (length = size), each ±1.
 * @param inputs   Input vector (length = size), each ±1.
 * @param size     Vector dimension S.
 * @return         Dot-product result.
 */
ss_dot_result_t ss_dot_bnn(const ss_hal_state_t *state,
                            const ss_weight_t *weights,
                            const ss_input_t *inputs,
                            int size);

/**
 * @brief Compute a single TBN dot-product.
 *
 * Applies TBN formula: P = 2·CNT_out − (S − Z)  (Eq. 2).
 * Inputs may be ternary {-1, 0, +1}. Zero inputs are detected
 * by the ZID circuit and excluded from the count.
 *
 * @param state    HAL state (must be initialised, mode = TBN).
 * @param weights  Weight vector (length = size), each ±1.
 * @param inputs   Input vector (length = size), each {-1, 0, +1}.
 * @param size     Vector dimension S.
 * @return         Dot-product result.
 */
ss_dot_result_t ss_dot_tbn(const ss_hal_state_t *state,
                            const ss_weight_t *weights,
                            const ss_input_t *inputs,
                            int size);

/**
 * @brief Auto-mode dot-product: dispatches to BNN or TBN based on HAL mode.
 */
ss_dot_result_t ss_dot_auto(const ss_hal_state_t *state,
                             const ss_weight_t *weights,
                             const ss_input_t *inputs,
                             int size);

/* ===================================================================== */
/* Zero Input Detection (ZID)                                            */
/* ===================================================================== */

/**
 * @brief Count zeros in an input vector (software ZID emulation).
 *
 * Implements the NOR-gate logic of the ZID circuit (FIG 22):
 *   For each word-line pair, NOR(V1−Vread, V2−Vread).
 *   If both at Vread → zero input → count++.
 *
 * @param inputs  Input vector.
 * @param size    Vector dimension.
 * @return        Number of zero inputs Z.
 */
int ss_zid_count_zeros(const ss_input_t *inputs, int size);

/**
 * @brief Generate ZID bitmap for an input vector.
 *
 * Sets bit N in the bitmap if inputs[N] == 0.
 * The bitmap is stored as a uint32_t array matching the MMIO
 * ZID bitmap register layout.
 *
 * @param inputs  Input vector.
 * @param size    Vector dimension.
 * @param bitmap  Output bitmap (caller allocates, ceil(size/32) uint32_ts).
 */
void ss_zid_bitmap(const ss_input_t *inputs, int size, uint32_t *bitmap);

/* ===================================================================== */
/* Matrix-Vector Multiplication                                          */
/* ===================================================================== */

/**
 * @brief Multiply weight matrix by input vector.
 *
 * Computes y[i] = dot(W[i,:], x) for each row i of W.
 * Uses BNN or TBN formula based on HAL mode.
 *
 * On hardware, each row maps to one bit line (NAND string), and
 * all rows are computed in parallel via sense amplifiers.
 *
 * @param state    HAL state.
 * @param weights  Weight matrix [rows × cols], row-major. Each ±1.
 * @param inputs   Input vector (length = cols).
 * @param rows     Number of output neurons (M).
 * @param cols     Input vector dimension (S).
 * @param outputs  Output array (length = rows, caller allocates).
 * @return         0 on success, -1 on failure.
 */
int ss_matmul(const ss_hal_state_t *state,
              const ss_weight_t *weights,
              const ss_input_t *inputs,
              int rows, int cols,
              int *outputs);

/* ===================================================================== */
/* Activation Functions                                                  */
/* ===================================================================== */

/**
 * @brief Sign activation for BNN: output = sign(x).
 *
 * Maps real-valued dot-product to binary output:
 *   x > 0  → +1
 *   x == 0 → +1 (convention: ties go to +1)
 *   x < 0  → -1
 *
 * @param x  Dot-product value.
 * @return   Binary output (+1 or -1).
 */
static inline ss_input_t ss_activation_sign(int x)
{
    return (x >= 0) ? SS_INPUT_POS : SS_INPUT_NEG;
}

/**
 * @brief Ternary activation for TBN: output = sign(x) with deadzone.
 *
 * Maps real-valued dot-product to ternary output:
 *   x > threshold  → +1
 *   x < -threshold → -1
 *   otherwise      →  0
 *
 * The threshold models the "uncertainty band" for ternary quantisation.
 *
 * @param x          Dot-product value.
 * @param threshold  Deadzone width (≥0).
 * @return           Ternary output {-1, 0, +1}.
 */
static inline ss_input_t ss_activation_ternary(int x, int threshold)
{
    if (x > threshold) return SS_INPUT_POS;
    if (x < -threshold) return SS_INPUT_NEG;
    return SS_INPUT_ZERO;
}

/* ===================================================================== */
/* Multi-Layer DNN Inference                                             */
/* ===================================================================== */

/**
 * @brief Run inference through multiple DNN layers.
 *
 * For each layer l in [0, num_layers):
 *   1. Compute y = W_l · x using ss_matmul()
 *   2. Apply activation function to each y[i]
 *   3. Use activated y as input x for next layer
 *
 * When pipelining is enabled, layers are mapped to different
 * planes and computed concurrently (FIG 30 of patent).
 *
 * @param state      HAL state.
 * @param config     DNN configuration (layers, parallelism).
 * @param input      Input vector for first layer.
 * @param input_size Size of the input vector.
 * @param output     Output buffer for final layer (caller allocates).
 * @param output_size Size of output buffer (must >= last layer rows).
 * @param threshold  Activation threshold (0 for sign, >0 for ternary).
 * @return           0 on success, -1 on failure.
 */
int ss_dnn_inference(const ss_hal_state_t *state,
                     const ss_dnn_config_t *config,
                     const ss_input_t *input, int input_size,
                     int *output, int output_size,
                     int threshold);

/* ===================================================================== */
/* Utility: Weight Matrix Programming                                    */
/* ===================================================================== */

/**
 * @brief Program a weight matrix into the NAND array.
 *
 * Each weight is stored as a unit synapse (pair of SLC cells)
 * in the NAND array. Row i → NAND string (bit line) i.
 * Column j → word-line pair j on each string.
 *
 * @param state    HAL state.
 * @param weights  Weight matrix [rows × cols], row-major. Each ±1.
 * @param rows     Number of rows (bit lines / output neurons).
 * @param cols     Number of columns (word-line pairs / input synapses).
 * @param block_id Target block index (0-based).
 * @return         0 on success, -1 on failure.
 */
int ss_program_weights(ss_hal_state_t *state,
                       const ss_weight_t *weights,
                       int rows, int cols,
                       int block_id);

/**
 * @brief Read back weights from the NAND array.
 *
 * @param state    HAL state.
 * @param weights  Output buffer [rows × cols] (caller allocates).
 * @param rows     Number of rows.
 * @param cols     Number of columns.
 * @param block_id Source block index.
 * @return         0 on success, -1 on failure.
 */
int ss_read_weights(const ss_hal_state_t *state,
                    ss_weight_t *weights,
                    int rows, int cols,
                    int block_id);

#ifdef __cplusplus
}
#endif

#endif /* SET5_SAMSUNG_TBN_H */
