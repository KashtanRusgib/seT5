/**
 * @file trit_tmvm.c
 * @brief seT6 Ternary Matrix-Vector Multiply Accelerator — implementation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_tmvm.h"
#include <string.h>

/* ==== Public API ======================================================= */

int tmvm_init(tmvm_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int tmvm_load_matrix(tmvm_state_t *st, const trit *mat, int rows, int cols) {
    if (!st || !st->initialized || !mat) return -1;
    if (rows <= 0 || rows > TMVM_MAX_DIM) return -1;
    if (cols <= 0 || cols > TMVM_MAX_DIM) return -1;

    st->rows = rows;
    st->cols = cols;
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            trit v = mat[r * cols + c];
            if (v < -1 || v > 1) v = TRIT_UNKNOWN; /* sanitize */
            st->matrix[r][c] = v;
        }
    }
    return 0;
}

int tmvm_load_vector(tmvm_state_t *st, const trit *vec, int len) {
    if (!st || !st->initialized || !vec) return -1;
    if (len <= 0 || len > TMVM_MAX_DIM) return -1;
    if (st->cols > 0 && len != st->cols) return -1; /* dimension mismatch */

    st->vec_len = len;
    for (int i = 0; i < len; i++) {
        trit v = vec[i];
        if (v < -1 || v > 1) v = TRIT_UNKNOWN;
        st->vector[i] = v;
    }
    return 0;
}

int tmvm_compress_32(tmvm_compressor_t *comp) {
    if (!comp) return -1;

    int a = comp->inputs[0];
    int b = comp->inputs[1];
    int c = comp->inputs[2];

    /*
     * (3;2) compressor in balanced ternary:
     * sum   = (a + b + c) mod 3  (balanced: wrap to {-1,0,+1})
     * carry = (a + b + c) / 3    (integer division, NDR-accelerated)
     *
     * This reduces 3 partial products to 2 values (sum + carry)
     * vs. binary which needs a 4:2 compressor chain.
     */
    int total = a + b + c;

    /* Balanced ternary: values in [-3, +3] */
    if (total >= 2) {
        comp->carry = 1;
        comp->sum = total - 3;
    } else if (total <= -2) {
        comp->carry = -1;
        comp->sum = total + 3;
    } else {
        comp->carry = 0;
        comp->sum = total;
    }

    comp->stages_used = 1;
    return 0;
}

int tmvm_dot_sparse(const trit *a, const trit *b, int len, int *skips) {
    if (!a || !b || len <= 0) return 0;

    int acc = 0;
    int skip_count = 0;

    for (int i = 0; i < len; i++) {
        if (a[i] == 0 || b[i] == 0) {
            skip_count++;
            continue; /* Sparsity skip: 0 × anything = 0 */
        }
        /* Ternary MAC: {-1,+1} × {-1,+1} → {-1,+1} */
        acc += a[i] * b[i];
    }

    if (skips) *skips = skip_count;
    return acc;
}

int tmvm_execute(tmvm_state_t *st) {
    if (!st || !st->initialized) return -1;
    if (st->rows <= 0 || st->cols <= 0 || st->vec_len <= 0) return -1;
    if (st->vec_len != st->cols) return -1;

    st->total_macs = 0;
    st->sparse_skips = 0;
    st->compressor_stages = 0;
    st->energy_aj = 0;
    st->energy_binary_aj = 0;

    for (int r = 0; r < st->rows; r++) {
        int skips = 0;
        int dot = tmvm_dot_sparse(st->matrix[r], st->vector,
                                   st->cols, &skips);
        st->result[r] = dot;
        st->sparse_skips += skips;
        int real_macs = st->cols - skips;
        st->total_macs += real_macs;

        /* (3;2) compressor stages: ceil(real_macs / 3) per reduction */
        if (real_macs > 0) {
            int stages = (real_macs + 2) / 3;  /* ceiling division */
            st->compressor_stages += stages;
        }

        /* Energy model */
        st->energy_aj += (int64_t)real_macs * TMVM_ENERGY_PER_MAC_AJ;
        st->energy_binary_aj += (int64_t)st->cols * TMVM_ENERGY_BINARY_AJ;
    }

    st->result_len = st->rows;

    /* Compute sparsity percentage */
    int total_possible = st->rows * st->cols;
    if (total_possible > 0) {
        st->sparsity_pct = (st->sparse_skips * 100) / total_possible;
    }

    /* Compute PDP gain */
    if (st->energy_binary_aj > 0) {
        st->pdp_gain_pct = 100 - (int)(
            (st->energy_aj * 100) / st->energy_binary_aj
        );
    }

    return 0;
}

int tmvm_get_pdp_gain(const tmvm_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->pdp_gain_pct;
}

int tmvm_get_sparsity(const tmvm_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->sparsity_pct;
}

int tmvm_dlt_quant(tmvm_state_t *st, const int *weights, const trit *vec,
                   int rows, int cols, int wp, int wn, int delta) {
    if (!st || !st->initialized || !weights || !vec) return -1;
    if (rows <= 0 || rows > TMVM_MAX_DIM) return -1;
    if (cols <= 0 || cols > TMVM_MAX_DIM) return -1;

    int pos_thresh = wp + delta;
    int neg_thresh = wn + delta;
    int trapped = 0;

    /* Quantize weight matrix to trit using DLT thresholds and load */
    trit qmat[TMVM_MAX_DIM * TMVM_MAX_DIM];
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            int w = weights[r * cols + c];
            if (w > pos_thresh)
                qmat[r * cols + c] = TRIT_TRUE;
            else if (w < neg_thresh)
                qmat[r * cols + c] = TRIT_FALSE;
            else {
                qmat[r * cols + c] = TRIT_UNKNOWN;
                trapped++;
            }
        }
    }

    /* Load quantized matrix and vector, then execute */
    tmvm_load_matrix(st, qmat, rows, cols);
    tmvm_load_vector(st, vec, cols);
    tmvm_execute(st);

    return trapped;
}
