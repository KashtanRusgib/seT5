/**
 * @file trit_ai.c
 * @brief Trit Linux — Advanced AI/ML Integration Implementation
 *
 * Implements ternary matrix-vector multiplication, inference engine,
 * and ternary SGD training. Uses multi-radix DOT_TRIT for acceleration.
 *
 * Enhancement 5: "Advanced AI/ML Integration and Tooling"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include "trit_ai.h"

/* ==================================================================== */
/*  Model Management                                                    */
/* ==================================================================== */

int tai_model_init(tai_model_t *model) {
    if (!model) return TAI_ERR_INIT;

    memset(model, 0, sizeof(*model));
    multiradix_init(&model->mr);
    model->initialized = 1;

    return TAI_OK;
}

int tai_add_layer(tai_model_t *model, int input_dim, int output_dim) {
    if (!model || !model->initialized) return TAI_ERR_INIT;
    if (model->layer_count >= TAI_MAX_LAYERS) return TAI_ERR_OVERFLOW;
    if (input_dim <= 0 || output_dim <= 0) return TAI_ERR_DIM;
    if (input_dim > TAI_MAX_COLS || output_dim > TAI_MAX_ROWS) return TAI_ERR_DIM;

    tai_layer_t *layer = &model->layers[model->layer_count];
    memset(layer, 0, sizeof(*layer));

    layer->input_dim = input_dim;
    layer->output_dim = output_dim;
    layer->weights.rows = output_dim;
    layer->weights.cols = input_dim;

    /* Initialize bias vector dimensions */
    layer->bias.len = output_dim;

    /* Weights default to TRIT_UNKNOWN (0) = no contribution */
    model->layer_count++;
    return TAI_OK;
}

int tai_set_weight(tai_model_t *model, int layer, int row, int col, trit value) {
    if (!model || !model->initialized) return TAI_ERR_INIT;
    if (layer < 0 || layer >= model->layer_count) return TAI_ERR_DIM;

    tai_layer_t *l = &model->layers[layer];
    if (row < 0 || row >= l->weights.rows) return TAI_ERR_DIM;
    if (col < 0 || col >= l->weights.cols) return TAI_ERR_DIM;

    l->weights.data[row * l->weights.cols + col] = value;
    return TAI_OK;
}

int tai_set_bias(tai_model_t *model, int layer, int row, int value) {
    if (!model || !model->initialized) return TAI_ERR_INIT;
    if (layer < 0 || layer >= model->layer_count) return TAI_ERR_DIM;

    tai_layer_t *l = &model->layers[layer];
    if (row < 0 || row >= l->output_dim) return TAI_ERR_DIM;

    l->bias.data[row] = value;
    return TAI_OK;
}

/* ==================================================================== */
/*  Matrix/Vector Operations                                            */
/* ==================================================================== */

int tai_matvec(const tai_matrix_t *mat, const tai_vector_t *vec,
               tai_int_vector_t *out) {
    if (!mat || !vec || !out) return TAI_ERR_INIT;
    if (mat->cols != vec->len) return TAI_ERR_DIM;

    out->len = mat->rows;

    /*
     * Ternary matrix-vector multiply: for each row, compute dot product
     * with the input vector. Since weights are in {-1,0,+1}, each
     * multiply is trivial: -1*x=-x, 0*x=0, +1*x=x. This is the core
     * efficiency advantage of ternary neural networks.
     */
    for (int r = 0; r < mat->rows; r++) {
        int sum = 0;
        for (int c = 0; c < mat->cols; c++) {
            trit w = mat->data[r * mat->cols + c];
            trit x = vec->data[c];
            /* Ternary multiply: result is product of two trits */
            sum += (int)w * (int)x;
        }
        out->data[r] = sum;
    }

    return TAI_OK;
}

int tai_dot(const tai_vector_t *a, const tai_vector_t *b) {
    if (!a || !b) return 0;

    int len = (a->len < b->len) ? a->len : b->len;
    int sum = 0;

    /*
     * Ternary dot product: element-wise multiply-accumulate.
     * Since both vectors are in {-1,0,+1}, each product is in {-1,0,+1}.
     */
    for (int i = 0; i < len; i++) {
        sum += (int)a->data[i] * (int)b->data[i];
    }

    return sum;
}

int tai_matvec_mr(tai_model_t *model,
                  const tai_matrix_t *mat, const tai_vector_t *vec,
                  tai_int_vector_t *out) {
    if (!model || !mat || !vec || !out) return TAI_ERR_INIT;
    if (mat->cols != vec->len) return TAI_ERR_DIM;

    out->len = mat->rows;

    /*
     * Multi-radix accelerated matmul: load vector into register 0,
     * each row into register 1, then use dot_trit for the product.
     * This exploits structured sparsity in ternary weights.
     */

    /* Load input vector into MR register 0 */
    model->mr.regs[0] = trit2_reg32_splat(TRIT2_UNKNOWN);
    for (int c = 0; c < vec->len && c < MR_REG_WIDTH; c++) {
        trit2_reg32_set(&model->mr.regs[0], c, trit2_encode(vec->data[c]));
    }

    for (int r = 0; r < mat->rows; r++) {
        /* Load row r into MR register 1 */
        model->mr.regs[1] = trit2_reg32_splat(TRIT2_UNKNOWN);
        for (int c = 0; c < mat->cols && c < MR_REG_WIDTH; c++) {
            trit w = mat->data[r * mat->cols + c];
            trit2_reg32_set(&model->mr.regs[1], c, trit2_encode(w));
        }

        /* Compute dot product using multi-radix engine */
        out->data[r] = dot_trit(&model->mr, 0, 1);

        /* Track sparsity skips */
        model->sparse_skips += model->mr.dot_sparse_skip;
    }

    model->total_macs += mat->rows * mat->cols;

    return TAI_OK;
}

/* ==================================================================== */
/*  Inference                                                           */
/* ==================================================================== */

int tai_infer(tai_model_t *model, const tai_vector_t *input,
              tai_int_vector_t *output) {
    if (!model || !input || !output || !model->initialized) return TAI_ERR_INIT;
    if (model->layer_count == 0) return TAI_ERR_NODATA;

    /*
     * Forward pass through all layers:
     *   For each layer, compute output = W * input + bias.
     *   The output of one layer becomes the (quantized) input of the next.
     *   Final layer output is returned as integer vector.
     */

    /* Use input as the first layer's input */
    tai_vector_t current_input = *input;
    tai_int_vector_t layer_output;

    for (int l = 0; l < model->layer_count; l++) {
        tai_layer_t *layer = &model->layers[l];

        /* Verify dimension compatibility */
        if (current_input.len != layer->input_dim) return TAI_ERR_DIM;

        /* Matrix-vector multiply */
        int rc = tai_matvec(&layer->weights, &current_input, &layer_output);
        if (rc != TAI_OK) return rc;

        /* Add bias */
        for (int i = 0; i < layer_output.len; i++) {
            layer_output.data[i] += layer->bias.data[i];
        }

        layer->activated = 1;
        model->total_macs += layer->output_dim * layer->input_dim;

        /*
         * If not the last layer, quantize output back to ternary for the
         * next layer's input. Activation: sign function (ternary step).
         *   positive → +1 (True)
         *   zero     →  0 (Unknown)
         *   negative → -1 (False)
         */
        if (l < model->layer_count - 1) {
            current_input.len = layer_output.len;
            for (int i = 0; i < layer_output.len; i++) {
                if (layer_output.data[i] > 0)      current_input.data[i] = TRIT_TRUE;
                else if (layer_output.data[i] < 0)  current_input.data[i] = TRIT_FALSE;
                else                                 current_input.data[i] = TRIT_UNKNOWN;
            }
        }
    }

    /* Return final layer output */
    *output = layer_output;
    model->inferences++;

    return TAI_OK;
}

int tai_argmax(const tai_int_vector_t *vec) {
    if (!vec || vec->len == 0) return -1;

    int max_idx = 0;
    int max_val = vec->data[0];

    for (int i = 1; i < vec->len; i++) {
        if (vec->data[i] > max_val) {
            max_val = vec->data[i];
            max_idx = i;
        }
    }

    return max_idx;
}

/* ==================================================================== */
/*  Training — Ternary SGD                                              */
/* ==================================================================== */

int tai_train_step(tai_model_t *model, const tai_vector_t *input,
                   int target_class, const tai_train_config_t *config) {
    if (!model || !input || !config || !model->initialized) return TAI_ERR_INIT;
    if (model->layer_count == 0) return TAI_ERR_NODATA;

    /*
     * Simple ternary SGD step:
     * 1. Forward pass to get predictions
     * 2. Compute error signal (target vs predicted)
     * 3. Update weights using ternary gradient approximation
     *
     * Ternary gradient: for weight w and error e, update rule is:
     *   w' = clamp(w + sign(e * x), {-1, 0, +1})
     *
     * This keeps weights in the ternary set after each update.
     */

    /* Forward pass */
    tai_int_vector_t output;
    int rc = tai_infer(model, input, &output);
    if (rc != TAI_OK) return rc;

    /* Compute error for last layer (one-hot target) */
    tai_layer_t *last = &model->layers[model->layer_count - 1];
    for (int r = 0; r < last->output_dim && r < output.len; r++) {
        int target_val = (r == target_class) ? 1 : 0;
        int error = target_val - (output.data[r] > 0 ? 1 : 0);

        if (error == 0) continue; /* No update needed */

        /*
         * Update weights in the last layer:
         * For each weight w[r][c], compute gradient estimate:
         *   grad = sign(error) * sign(input[c])
         * Then: w' = clamp(w + grad, {-1, 0, +1})
         *
         * Learning rate is implicit in the clamp operation:
         * ternary weights can only change by 1 step per update.
         */
        for (int c = 0; c < last->input_dim && c < input->len; c++) {
            int grad = error * ((input->data[c] > 0) ? 1 :
                               (input->data[c] < 0) ? -1 : 0);
            if (grad == 0) continue;

            int w_idx = r * last->weights.cols + c;
            int new_w = (int)last->weights.data[w_idx] + (grad > 0 ? 1 : -1);

            /* Clamp to ternary range {-1, 0, +1} */
            if (new_w > 1)  new_w = 1;
            if (new_w < -1) new_w = -1;
            last->weights.data[w_idx] = (trit)new_w;
        }

        /* Update bias */
        last->bias.data[r] += (error > 0) ? 1 : -1;
    }

    return TAI_OK;
}

/* ==================================================================== */
/*  Statistics                                                          */
/* ==================================================================== */

void tai_stats(const tai_model_t *model,
               int *inferences, int *macs, int *sparse_skips) {
    if (!model) return;
    if (inferences)  *inferences  = model->inferences;
    if (macs)        *macs        = model->total_macs;
    if (sparse_skips)*sparse_skips= model->sparse_skips;
}

int tai_sparsity(const tai_model_t *model, int layer) {
    if (!model || layer < 0 || layer >= model->layer_count) return 0;

    const tai_layer_t *l = &model->layers[layer];
    int total = l->weights.rows * l->weights.cols;
    if (total == 0) return 0;

    /* Count zero (Unknown) weights */
    int zeros = 0;
    for (int i = 0; i < total; i++) {
        if (l->weights.data[i] == TRIT_UNKNOWN) zeros++;
    }

    /* Return sparsity as percentage × 100 (e.g. 5000 = 50%) */
    return (zeros * 10000) / total;
}
