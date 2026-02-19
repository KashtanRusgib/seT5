/**
 * @file trit_resisc.c
 * @brief seT6 ResISC — Residue-domain In-Sensor Computing — implementation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_resisc.h"
#include <string.h>
#include <stdlib.h>

/* ==== Helpers =========================================================== */

/** Count 1-bits in a 32-bit word (popcount). */
static int popcount32(uint32_t x) {
    int c = 0;
    while (x) { c += (int)(x & 1); x >>= 1; }
    return c;
}

/**
 * Decode a bit-stream to a trit value based on 1-density:
 *   density > 0.66 → +1,  density < 0.33 → -1,  else → 0.
 */
static trit bitstream_to_trit(uint32_t stream) {
    int ones = popcount32(stream);
    if (ones > 21)  return 1;   /* >66% ones → +1 */
    if (ones < 11)  return -1;  /* <33% ones → -1 */
    return 0;
}

/**
 * Encode a trit to an RNS residue vector (same as tmvm_rns helper).
 */
static void trit_to_rns_residues(trit t, trit_rns_t *out,
                                  const trit_rns_context_t *ctx) {
    for (uint32_t k = 0; k < ctx->count; k++) {
        if (t == 0)       out->residues[k] = 0;
        else if (t == 1)  out->residues[k] = 1;
        else              out->residues[k] = ctx->moduli[k] - 1;
    }
    for (uint32_t k = ctx->count; k < RNS_MAX_MODULI; k++)
        out->residues[k] = 0;
}

/**
 * CRT reconstruct an RNS residue to signed integer.
 */
static int resisc_crt_reconstruct(const trit_rns_t *rns,
                                   const trit_rns_context_t *ctx) {
    int64_t x = 0;
    for (uint32_t k = 0; k < ctx->count; k++) {
        x += (int64_t)rns->residues[k] * ctx->Mi[k] * ctx->Mi_inv[k];
    }
    int val = (int)(x % (int64_t)ctx->M);
    if ((uint32_t)val > ctx->M / 2)
        val -= (int)ctx->M;
    return val;
}

/* ==== Public API ======================================================== */

int resisc_init(resisc_state_t *st, const trit_rns_context_t *ctx) {
    if (!st || !ctx) return -1;
    memset(st, 0, sizeof(*st));
    st->rns_ctx = *ctx;
    st->initialized = 1;
    return 0;
}

int resisc_encode_pixels(resisc_state_t *st, const trit *pixels, int count) {
    if (!st || !st->initialized || !pixels) return -1;
    if (count <= 0 || count > RESISC_MAX_PIXELS) return -1;

    st->pixel_count = count;
    for (int i = 0; i < count; i++) {
        trit v = pixels[i];
        if (v < -1 || v > 1) v = 0;

        resisc_pixel_t *px = &st->pixels[i];
        px->trit_value = v;

        /* Deterministic bit-stream encoding */
        if (v == 1)
            px->stream = 0xFFFFFFFFu;      /* all 1s → +1 */
        else if (v == -1)
            px->stream = 0x00000000u;       /* all 0s → -1 */
        else
            px->stream = 0x55555555u;       /* alternating → 0 */

        px->ones_count = popcount32(px->stream);

        /* Sensing energy */
        st->energy_sense_fj += RESISC_ENERGY_SENSE_FJ;
    }
    return 0;
}

int resisc_load_weights(resisc_state_t *st, const trit *weights, int count) {
    if (!st || !st->initialized || !weights) return -1;
    if (count <= 0 || count > RESISC_MAX_WEIGHTS) return -1;

    st->weight_count = count;
    for (int i = 0; i < count; i++) {
        trit v = weights[i];
        if (v < -1 || v > 1) v = 0;
        st->weights[i] = v;
    }
    return 0;
}

int resisc_execute(resisc_state_t *st) {
    if (!st || !st->initialized) return -1;
    if (st->pixel_count <= 0 || st->weight_count <= 0) return -1;

    int out_count = st->pixel_count - st->weight_count + 1;
    if (out_count <= 0) out_count = 1;
    if (out_count > RESISC_MAX_PIXELS) out_count = RESISC_MAX_PIXELS;

    st->result_count = out_count;
    st->energy_compute_fj = 0;
    st->energy_saved_fj = 0;

    for (int i = 0; i < out_count; i++) {
        /* Initialize RNS accumulator to zero */
        memset(&st->rns_accum[i], 0, sizeof(trit_rns_t));

        for (int k = 0; k < st->weight_count; k++) {
            int px_idx = i + k;
            if (px_idx >= st->pixel_count) break;

            trit pv = st->pixels[px_idx].trit_value;
            trit wv = st->weights[k];

            /* Per-channel MAC in residue domain */
            trit_rns_t px_rns, wt_rns;
            trit_to_rns_residues(pv, &px_rns, &st->rns_ctx);
            trit_to_rns_residues(wv, &wt_rns, &st->rns_ctx);

            for (uint32_t ch = 0; ch < st->rns_ctx.count; ch++) {
                uint32_t prod = (px_rns.residues[ch] * wt_rns.residues[ch])
                               % st->rns_ctx.moduli[ch];
                st->rns_accum[i].residues[ch] =
                    (st->rns_accum[i].residues[ch] + prod)
                    % st->rns_ctx.moduli[ch];
            }

            st->energy_compute_fj += RESISC_ENERGY_MAC_FJ;
        }

        /* CRT reconstruct */
        st->results[i] = resisc_crt_reconstruct(&st->rns_accum[i],
                                                  &st->rns_ctx);

        /* Energy saved: no ADC needed per pixel in this window */
        st->energy_saved_fj += (int64_t)st->weight_count * RESISC_ENERGY_ADC_FJ;
    }

    /* SNR estimate: for clean signals, SNR ≈ 6.02 * bits + 1.76 */
    st->snr_db = 6 * RESISC_BITSTREAM_LEN + 2; /* ~194 dB for 32-bit */
    if (st->bit_errors > 0) {
        /* Degrade SNR based on error count */
        int degrade = st->bit_errors * 3;
        st->snr_db = (st->snr_db > degrade) ? st->snr_db - degrade : 1;
    }

    return 0;
}

int64_t resisc_get_energy(const resisc_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->energy_sense_fj + st->energy_compute_fj;
}

int64_t resisc_get_energy_saved(const resisc_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->energy_saved_fj;
}

int resisc_get_snr(const resisc_state_t *st) {
    if (!st || !st->initialized) return 0;
    return st->snr_db;
}

int resisc_inject_noise(resisc_state_t *st, double error_rate) {
    if (!st || !st->initialized) return -1;
    if (error_rate < 0.0 || error_rate > 1.0) return -1;

    int errors = 0;

    for (int i = 0; i < st->pixel_count; i++) {
        resisc_pixel_t *px = &st->pixels[i];
        uint32_t original = px->stream;

        for (int b = 0; b < RESISC_BITSTREAM_LEN; b++) {
            double r = (double)rand() / (double)RAND_MAX;
            if (r < error_rate) {
                px->stream ^= (1u << b);  /* flip bit */
            }
        }

        if (px->stream != original) {
            /* Re-decode the corrupted stream */
            trit new_val = bitstream_to_trit(px->stream);
            if (new_val != px->trit_value) {
                errors++;
            }
            px->ones_count = popcount32(px->stream);
        }
    }

    st->bit_errors += errors;
    return errors;
}
