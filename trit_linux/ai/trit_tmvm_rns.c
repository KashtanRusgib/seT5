/**
 * @file trit_tmvm_rns.c
 * @brief seT6 TMVM+RNS Integration — implementation.
 *
 * Performs matrix-vector multiply in the RNS residue domain.
 * Each RNS channel accumulates independently with no carries,
 * then CRT reconstructs the final integer result.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_tmvm_rns.h"
#include <string.h>

/* ==== Helpers =========================================================== */

/**
 * Encode a balanced trit {-1, 0, +1} into RNS residue form.
 * -1 maps to (modulus - 1) for each channel.
 */
static void encode_trit_to_rns(trit t, trit_rns_t *out,
                                const trit_rns_context_t *ctx) {
    for (uint32_t k = 0; k < ctx->count; k++) {
        if (t == 0)
            out->residues[k] = 0;
        else if (t == 1)
            out->residues[k] = 1;
        else  /* t == -1 */
            out->residues[k] = ctx->moduli[k] - 1;
    }
    for (uint32_t k = ctx->count; k < RNS_MAX_MODULI; k++)
        out->residues[k] = 0;
}

/**
 * CRT reconstruction from RNS residues to integer.
 * Returns signed result in [-M/2, M/2].
 */
static int crt_reconstruct(const trit_rns_t *rns,
                            const trit_rns_context_t *ctx,
                            int channels) {
    int64_t x = 0;
    uint32_t ch = (uint32_t)channels;
    if (ch > ctx->count) ch = ctx->count;

    /* Partial dynamic range for truncated channels */
    uint32_t M_partial = 1;
    for (uint32_t k = 0; k < ch; k++)
        M_partial *= ctx->moduli[k];

    for (uint32_t k = 0; k < ch; k++) {
        uint32_t Mi_k = M_partial / ctx->moduli[k];
        /* Recompute Mi_inv for partial product if truncated */
        uint32_t inv = ctx->Mi_inv[k];
        if (ch != ctx->count) {
            /* Simple brute-force inverse for small moduli */
            inv = 0;
            for (uint32_t t = 1; t < ctx->moduli[k]; t++) {
                if ((Mi_k * t) % ctx->moduli[k] == 1) { inv = t; break; }
            }
        }
        x += (int64_t)rns->residues[k] * Mi_k * inv;
    }
    int val = (int)(x % (int64_t)M_partial);
    /* Convert to signed */
    if ((uint32_t)val > M_partial / 2)
        val -= (int)M_partial;
    return val;
}

/* ==== Public API ======================================================== */

int tmvm_rns_init(tmvm_rns_state_t *st, const trit_rns_context_t *ctx) {
    if (!st || !ctx) return -1;
    memset(st, 0, sizeof(*st));
    st->rns_ctx = *ctx;
    st->active_channels = (int)ctx->count;
    st->area_save_pct = TMVM_RNS_AREA_SAVE_PCT;
    st->initialized = 1;
    return 0;
}

int tmvm_rns_load_matrix(tmvm_rns_state_t *st, const trit *mat,
                         int rows, int cols) {
    if (!st || !st->initialized || !mat) return -1;
    if (rows <= 0 || rows > TMVM_RNS_MAX_DIM) return -1;
    if (cols <= 0 || cols > TMVM_RNS_MAX_DIM) return -1;

    st->rows = rows;
    st->cols = cols;
    for (int r = 0; r < rows; r++) {
        for (int c = 0; c < cols; c++) {
            trit v = mat[r * cols + c];
            if (v < -1 || v > 1) v = 0;
            encode_trit_to_rns(v, &st->matrix_rns[r][c], &st->rns_ctx);
        }
    }
    return 0;
}

int tmvm_rns_load_vector(tmvm_rns_state_t *st, const trit *vec, int len) {
    if (!st || !st->initialized || !vec) return -1;
    if (len <= 0 || len > TMVM_RNS_MAX_DIM) return -1;
    if (st->cols > 0 && len != st->cols) return -1;

    st->vec_len = len;
    for (int i = 0; i < len; i++) {
        trit v = vec[i];
        if (v < -1 || v > 1) v = 0;
        encode_trit_to_rns(v, &st->vector_rns[i], &st->rns_ctx);
    }
    return 0;
}

int tmvm_rns_dot(const trit_rns_t *a, const trit_rns_t *b,
                 int len, trit_rns_t *out, const trit_rns_context_t *ctx) {
    if (!a || !b || !out || !ctx || len <= 0) return -1;

    /* Zero-init accumulator */
    for (uint32_t k = 0; k < RNS_MAX_MODULI; k++)
        out->residues[k] = 0;

    for (int i = 0; i < len; i++) {
        for (uint32_t k = 0; k < ctx->count; k++) {
            uint32_t prod = (a[i].residues[k] * b[i].residues[k])
                            % ctx->moduli[k];
            out->residues[k] = (out->residues[k] + prod) % ctx->moduli[k];
        }
    }
    return 0;
}

int tmvm_rns_execute(tmvm_rns_state_t *st) {
    if (!st || !st->initialized) return -1;
    if (st->rows <= 0 || st->cols <= 0 || st->vec_len <= 0) return -1;
    if (st->vec_len != st->cols) return -1;

    st->total_channel_macs = 0;
    st->crt_reconstructions = 0;
    st->energy_aj = 0;

    int ch = st->active_channels;
    if (ch > (int)st->rns_ctx.count) ch = (int)st->rns_ctx.count;

    for (int r = 0; r < st->rows; r++) {
        trit_rns_t acc;
        memset(&acc, 0, sizeof(acc));

        for (int c = 0; c < st->cols; c++) {
            for (int k = 0; k < ch; k++) {
                uint32_t prod = (st->matrix_rns[r][c].residues[k]
                               * st->vector_rns[c].residues[k])
                               % st->rns_ctx.moduli[k];
                acc.residues[k] = (acc.residues[k] + prod)
                                 % st->rns_ctx.moduli[k];
            }
            st->total_channel_macs += ch;
        }

        /* CRT reconstruct */
        st->result[r] = crt_reconstruct(&acc, &st->rns_ctx, ch);
        st->crt_reconstructions++;

        /* Energy: channel MACs + one CRT */
        st->energy_aj += (int64_t)st->cols * ch * TMVM_RNS_ENERGY_PER_CH;
        st->energy_aj += TMVM_RNS_ENERGY_CRT;
    }

    st->result_len = st->rows;
    return 0;
}

int tmvm_rns_set_truncation(tmvm_rns_state_t *st, int channels) {
    if (!st || !st->initialized) return -1;
    if (channels < 1 || channels > (int)st->rns_ctx.count) return -1;
    st->active_channels = channels;
    return 0;
}

int tmvm_rns_get_area_save(const tmvm_rns_state_t *st) {
    if (!st || !st->initialized) return 0;
    /* Area save scales with truncation: fewer channels → more savings */
    int full = (int)st->rns_ctx.count;
    if (full == 0) return 0;
    int base_save = TMVM_RNS_AREA_SAVE_PCT;
    int extra = ((full - st->active_channels) * 10) / full;
    return base_save + extra;
}

int64_t tmvm_rns_get_energy(const tmvm_rns_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->energy_aj;
}
