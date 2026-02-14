/**
 * @file trit_ai.h
 * @brief Trit Linux — Advanced AI/ML Integration and Tooling Header
 *
 * Provides user-space wrappers for Ternary Matrix-Vector Multiplication
 * (TMVM), inference CLI interface, and ternary SGD training support.
 * Leverages TWTM (via DOT_TRIT) and the multi-radix engine for
 * accelerated ternary neural network operations.
 *
 * Enhancement 5 from LOGICAL_ENHANCEMENTS_FOR_TRIT_LINUX.md:
 *   "Advanced AI/ML Integration and Tooling"
 *
 * Key features:
 *   - TMVM: Ternary matrix-vector multiplication
 *   - Ternary inference engine (trit-infer)
 *   - Ternary SGD with DOT_TRIT gradients
 *   - Weight loading/saving via TFS
 *   - Accuracy and latency benchmarking
 *   - Extreme quantization (BitNet b1.58 via TWQ)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_AI_H
#define TRIT_LINUX_TRIT_AI_H

#include "set5/trit.h"
#include "set5/multiradix.h"
#include "set5/ternary_weight_quantizer.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TAI_MAX_ROWS         64    /* Max matrix rows                       */
#define TAI_MAX_COLS         64    /* Max matrix columns                    */
#define TAI_MAX_LAYERS       8     /* Max neural network layers             */
#define TAI_MAX_WEIGHTS      4096  /* Max weights per layer                 */
#define TAI_BATCH_SIZE       16    /* Default mini-batch size               */

/* Error codes */
#define TAI_OK               0
#define TAI_ERR_INIT        (-1)
#define TAI_ERR_DIM         (-2)   /* Dimension mismatch */
#define TAI_ERR_OVERFLOW    (-3)
#define TAI_ERR_NODATA      (-4)

/* ==== Types ============================================================= */

/**
 * @brief Ternary matrix: rows x cols of trit values.
 *
 * Stored in row-major order. Used for weight matrices in
 * ternary neural networks.
 */
typedef struct {
    trit data[TAI_MAX_ROWS * TAI_MAX_COLS]; /**< Row-major trit data      */
    int  rows;                   /**< Number of rows                       */
    int  cols;                   /**< Number of columns                    */
} tai_matrix_t;

/**
 * @brief Ternary vector: up to MAX_COLS elements.
 */
typedef struct {
    trit data[TAI_MAX_COLS];     /**< Trit elements                        */
    int  len;                    /**< Active element count                  */
} tai_vector_t;

/**
 * @brief Integer result vector (for dot product outputs).
 */
typedef struct {
    int  data[TAI_MAX_ROWS];     /**< Integer results                      */
    int  len;                    /**< Active element count                  */
} tai_int_vector_t;

/**
 * @brief Neural network layer.
 *
 * Each layer has a weight matrix, bias vector, and activation function.
 * Weights are ternary ({-1,0,+1}); biases and outputs are integer.
 */
typedef struct {
    tai_matrix_t     weights;    /**< Weight matrix (rows x cols)          */
    tai_int_vector_t bias;       /**< Bias vector (one per output)         */
    int              input_dim;  /**< Input dimension                      */
    int              output_dim; /**< Output dimension                     */
    int              activated;  /**< 1 if layer has been forward-passed   */
} tai_layer_t;

/**
 * @brief Ternary neural network model.
 *
 * A stack of layers forming a feed-forward ternary network.
 * All weights are in {-1, 0, +1} for extreme quantization.
 */
typedef struct {
    tai_layer_t layers[TAI_MAX_LAYERS]; /**< Layer stack                   */
    int         layer_count;     /**< Number of layers                     */
    int         initialized;     /**< 1 = model ready                      */

    /* Multi-radix engine for DOT_TRIT acceleration */
    multiradix_state_t mr;

    /* Inference statistics */
    int         inferences;      /**< Total forward passes                 */
    int         total_macs;      /**< Total multiply-accumulate ops        */
    int         sparse_skips;    /**< Ops skipped via sparsity             */
} tai_model_t;

/**
 * @brief Training configuration for ternary SGD.
 */
typedef struct {
    int    epochs;               /**< Number of training epochs            */
    int    batch_size;           /**< Mini-batch size                      */
    int    learning_rate_x100;   /**< Learning rate × 100 (e.g. 10 = 0.1) */
    int    momentum_x100;        /**< Momentum × 100                      */
} tai_train_config_t;

/**
 * @brief Training result/statistics.
 */
typedef struct {
    int    epochs_completed;     /**< Epochs actually run                  */
    int    total_samples;        /**< Total samples processed              */
    int    correct;              /**< Correct predictions                  */
    int    accuracy_x100;        /**< Accuracy × 100 (percentage)         */
    int    loss_x100;            /**< Final loss × 100                    */
} tai_train_result_t;

/* ==== Model Management =================================================== */

/** Initialize a ternary neural network model */
int tai_model_init(tai_model_t *model);

/** Add a layer to the model */
int tai_add_layer(tai_model_t *model, int input_dim, int output_dim);

/** Set a weight in a specific layer */
int tai_set_weight(tai_model_t *model, int layer, int row, int col, trit value);

/** Set bias for a specific layer output */
int tai_set_bias(tai_model_t *model, int layer, int row, int value);

/* ==== Matrix/Vector Operations =========================================== */

/** Ternary matrix-vector multiplication (TMVM) */
int tai_matvec(const tai_matrix_t *mat, const tai_vector_t *vec,
               tai_int_vector_t *out);

/** Ternary dot product of two vectors */
int tai_dot(const tai_vector_t *a, const tai_vector_t *b);

/** Ternary matrix-vector multiplication using multi-radix DOT_TRIT */
int tai_matvec_mr(tai_model_t *model,
                  const tai_matrix_t *mat, const tai_vector_t *vec,
                  tai_int_vector_t *out);

/* ==== Inference ========================================================== */

/** Run forward inference through all layers */
int tai_infer(tai_model_t *model, const tai_vector_t *input,
              tai_int_vector_t *output);

/** Get argmax of an integer result vector (classification) */
int tai_argmax(const tai_int_vector_t *vec);

/* ==== Training =========================================================== */

/** Run ternary SGD training on a single sample */
int tai_train_step(tai_model_t *model, const tai_vector_t *input,
                   int target_class, const tai_train_config_t *config);

/* ==== Statistics ========================================================= */

/** Get model statistics */
void tai_stats(const tai_model_t *model,
               int *inferences, int *macs, int *sparse_skips);

/** Compute sparsity ratio (percentage of zero weights × 100) */
int tai_sparsity(const tai_model_t *model, int layer);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_AI_H */
