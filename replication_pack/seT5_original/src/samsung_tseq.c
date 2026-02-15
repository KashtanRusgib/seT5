/**
 * @file samsung_tseq.c
 * @brief Ternary Sequence Generation — Samsung CN105745888A
 *
 * Implements the base ternary sequence generation pipeline:
 *   1. m-sequence generation via LFSR
 *   2. m-sequence complement
 *   3. Cross-correlation for preferred pairs (Eq. 10)
 *   4. Perfect ternary sequence from shifted correlation (Fig. 6)
 *   5. Near-perfect ternary sequence via MSAC minimisation (Fig. 7)
 *   6. Base sequence formation by value insertion (§505)
 *   7. Hardcoded Table 3 sequences from the patent
 *   8. Codeset construction (all N cyclic shifts)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/samsung_tseq.h"
#include <string.h>
#include <math.h>

/* ===================================================================== */
/* Predefined Family Descriptors (patent Table 4)                        */
/* ===================================================================== */

static const tseq_family_t families[TSEQ_FAMILY_COUNT] = {
    { TSEQ_FAMILY_3_8,  3,  8, TSEQ_SEED_MSEQ, TSEQ_QUALITY_NEAR_PERFECT, "3/8-OOK"  },
    { TSEQ_FAMILY_4_16, 4, 16, TSEQ_SEED_MSEQ, TSEQ_QUALITY_NEAR_PERFECT, "4/16-OOK" },
    { TSEQ_FAMILY_5_32, 5, 32, TSEQ_SEED_MSEQ, TSEQ_QUALITY_NEAR_PERFECT, "5/32-OOK" },
};

const tseq_family_t *tseq_get_family(uint32_t family_id)
{
    if (family_id >= TSEQ_FAMILY_COUNT) return NULL;
    return &families[family_id];
}

/* ===================================================================== */
/* Primitive polynomials for LFSR m-sequence generation                  */
/* ===================================================================== */

/* Standard primitive polynomials in GF(2) for degrees 3-6.
 * Polynomial is represented as a bitmask: x^3 + x + 1 = 0b1011 = 0xB */
static const uint32_t lfsr_polys[] = {
    0,     /* degree 0 — unused */
    0,     /* degree 1 — unused */
    0x07,  /* degree 2: x^2 + x + 1 */
    0x0B,  /* degree 3: x^3 + x + 1      → period 7  */
    0x13,  /* degree 4: x^4 + x + 1      → period 15 */
    0x25,  /* degree 5: x^5 + x^2 + 1    → period 31 */
    0x43,  /* degree 6: x^6 + x + 1      → period 63 */
};

int tseq_gen_msequence(uint32_t n, uint32_t poly, tseq_seq_t *out)
{
    if (n < 2 || n > 6 || !out) return -1;

    uint32_t period = (1U << n) - 1;
    if (period > TSEQ_MAX_LEN) return -1;

    /* Use provided poly or default */
    uint32_t p = poly ? poly : lfsr_polys[n];

    /* LFSR state — start with all 1s */
    uint32_t state = (1U << n) - 1;

    for (uint32_t i = 0; i < period; i++) {
        /* Output bit = LSB */
        uint32_t bit = state & 1;
        /* Convert to bipolar: 0 → +1, 1 → -1 (standard convention) */
        out->data[i] = bit ? (tseq_elem_t)-1 : (tseq_elem_t)+1;

        /* Feedback */
        uint32_t fb = 0;
        uint32_t tmp = state & p;
        while (tmp) {
            fb ^= (tmp & 1);
            tmp >>= 1;
        }
        state = (state >> 1) | (fb << (n - 1));
    }

    out->len = period;
    return 0;
}

void tseq_complement(const tseq_seq_t *src, tseq_seq_t *dst)
{
    dst->len = src->len;
    for (uint32_t i = 0; i < src->len; i++) {
        dst->data[i] = (tseq_elem_t)(-src->data[i]);
    }
}

/* ===================================================================== */
/* Cross-Correlation (patent Eq. 10)                                     */
/* ===================================================================== */

int tseq_cross_correlation(const tseq_seq_t *x, const tseq_seq_t *y,
                           tseq_seq_t *out)
{
    if (!x || !y || !out || x->len != y->len) return -1;

    uint32_t P = x->len;
    out->len = P;

    for (uint32_t k = 0; k < P; k++) {
        int32_t sum = 0;
        for (uint32_t i = 0; i < P; i++) {
            /* θ(x,y)[k] = Σ (-1)^(x_i ⊕ y_{(i+k) mod P})
             * For bipolar {-1,+1}: product x_i * y_{(i+k) mod P}
             * gives +1 if same, -1 if different — equivalent to
             * (-1)^(XOR of original bits) */
            int32_t xi = (int32_t)x->data[i];
            int32_t yi = (int32_t)y->data[(i + k) % P];
            sum += xi * yi;
        }
        /* Clamp to tseq_elem_t range for storage;
         * actual cross-correlation may exceed [-1,+1] but
         * we store the full integer for computation. */
        out->data[k] = (tseq_elem_t)(sum > 127 ? 127 : (sum < -128 ? -128 : sum));
    }

    return 0;
}

/* ===================================================================== */
/* Perfect Ternary Sequence (patent Fig. 6, steps 601-604)               */
/* ===================================================================== */

/**
 * Generate decimated m-sequence for preferred pair.
 * The "d-th decimation" of sequence x is: y[i] = x[d*i mod P].
 */
static void decimate_sequence(const tseq_seq_t *src, uint32_t d,
                              tseq_seq_t *dst)
{
    uint32_t P = src->len;
    dst->len = P;
    for (uint32_t i = 0; i < P; i++)
        dst->data[i] = src->data[(d * i) % P];
}

int tseq_gen_perfect(const tseq_seq_t *seed, uint32_t decim,
                     tseq_seq_t *out)
{
    if (!seed || !out || seed->len < 3) return -1;

    uint32_t w = tseq_weight(seed);
    if (!tseq_is_perfect_square(w)) return -1;

    uint32_t P = seed->len;

    /* Step 601: get preferred pair — seed is x, decimation gives y */
    tseq_seq_t y;
    decimate_sequence(seed, decim ? decim : 3, &y);

    /* Step 602: compute cross-correlation θ(x, y) */
    tseq_seq_t theta;
    tseq_cross_correlation(seed, &y, &theta);

    /* Step 603: shifted correlation Ψ = 1 + θ */
    /* Step 604: divide by √(weight) to get Λ with elements {0, ±1} */
    uint32_t sqrt_w = 1;
    while (sqrt_w * sqrt_w < w) sqrt_w++;

    int32_t divisor = (int32_t)(sqrt_w > 0 ? sqrt_w : 1);

    out->len = P;
    for (uint32_t i = 0; i < P; i++) {
        int32_t psi = 1 + (int32_t)theta.data[i];
        int32_t lambda = psi / divisor;
        /* Clamp to {-1, 0, +1} */
        if (lambda > 1) lambda = 1;
        if (lambda < -1) lambda = -1;
        out->data[i] = (tseq_elem_t)lambda;
    }

    return 0;
}

/* ===================================================================== */
/* Near-Perfect Ternary Sequence (patent Fig. 7)                         */
/* ===================================================================== */

/**
 * Compute MSAC for a raw sequence stored as int32_t array.
 * Used internally during near-perfect generation.
 */
static double msac_raw(const tseq_elem_t *data, uint32_t len)
{
    if (len <= 1) return 0.0;

    double sum = 0.0;
    for (uint32_t tau = 1; tau < len; tau++) {
        int32_t r = 0;
        for (uint32_t i = 0; i < len; i++)
            r += (int32_t)data[i] * (int32_t)data[(i + tau) % len];
        sum += (double)r * (double)r;
    }
    return sum / (double)(len - 1);
}

int tseq_gen_near_perfect(const tseq_seq_t *seed,
                          double ratio_lo, double ratio_hi,
                          tseq_seq_t *out)
{
    if (!seed || !out || seed->len < 3) return -1;

    uint32_t P = seed->len;

    /* Start with the seed, try flipping non-zero positions to minimise MSAC.
     * We do a greedy search: for each non-zero position, try flipping it
     * and keep the change if MSAC decreases.  This is a practical
     * approximation of the patent's "all possible combinations" search
     * (which is exponential). */

    /* Copy seed into output */
    memcpy(out->data, seed->data, P * sizeof(tseq_elem_t));
    out->len = P;

    double best_msac = msac_raw(out->data, P);
    int improved = 1;

    while (improved) {
        improved = 0;
        for (uint32_t i = 0; i < P; i++) {
            if (out->data[i] == 0) continue;

            /* Try flipping this position */
            tseq_elem_t orig = out->data[i];
            out->data[i] = (tseq_elem_t)(-orig);

            /* Check ratio constraint */
            uint32_t neg_count = 0, pos_count = 0;
            for (uint32_t j = 0; j < P; j++) {
                if (out->data[j] < 0) neg_count++;
                else if (out->data[j] > 0) pos_count++;
            }

            double ratio = (pos_count > 0) ?
                           (double)neg_count / (double)pos_count : 999.0;

            if (ratio >= ratio_lo && ratio <= ratio_hi) {
                double new_msac = msac_raw(out->data, P);
                if (new_msac < best_msac) {
                    best_msac = new_msac;
                    improved = 1;
                } else {
                    out->data[i] = orig;  /* revert */
                }
            } else {
                out->data[i] = orig;  /* revert — ratio violated */
            }
        }
    }

    return 0;
}

/* ===================================================================== */
/* MSAC and Aperiodic Autocorrelation (patent Eq. 11-14)                 */
/* ===================================================================== */

double tseq_msac(const tseq_seq_t *seq)
{
    if (!seq || seq->len <= 1) return 0.0;
    return msac_raw(seq->data, seq->len);
}

int32_t tseq_aperiodic_autocorr(const tseq_seq_t *seq, uint32_t k)
{
    if (!seq || k >= seq->len) return 0;

    int32_t sum = 0;
    for (uint32_t i = 0; i + k < seq->len; i++)
        sum += (int32_t)seq->data[i] * (int32_t)seq->data[i + k];
    return sum;
}

/* ===================================================================== */
/* Base Ternary Sequence Formation (patent §505)                         */
/* ===================================================================== */

int tseq_gen_base(const tseq_seq_t *ternary,
                  tseq_seed_type_t seed_type,
                  tseq_seq_t *out,
                  uint32_t *best_pos)
{
    if (!ternary || !out || ternary->len < 2) return -1;

    uint32_t P = ternary->len;
    uint32_t N = P + 1;

    if (N > TSEQ_MAX_LEN) return -1;

    /* Predefined value to insert */
    tseq_elem_t insert_val = (seed_type == TSEQ_SEED_MSEQ)
                             ? (tseq_elem_t)0
                             : (tseq_elem_t)1;

    double best = 1e30;
    uint32_t best_p = 0;

    /* Try all positions (patent §505: position minimising MSAC) */
    tseq_seq_t candidate;
    candidate.len = N;

    for (uint32_t pos = 0; pos <= P; pos++) {
        /* Build candidate with insert_val at position pos */
        for (uint32_t i = 0; i < pos; i++)
            candidate.data[i] = ternary->data[i];
        candidate.data[pos] = insert_val;
        for (uint32_t i = pos; i < P; i++)
            candidate.data[i + 1] = ternary->data[i];

        /* Compute MSAC of ternary candidate */
        double m1 = msac_raw(candidate.data, N);

        /* Compute MSAC of |candidate| */
        tseq_seq_t abs_cand;
        tseq_abs_project(&candidate, &abs_cand);
        double m2 = msac_raw(abs_cand.data, N);

        /* Combined metric: minimise both (patent: "MSAC of base and |base|") */
        double combined = m1 + m2;

        if (combined < best) {
            best = combined;
            best_p = pos;
        }
    }

    /* Build final sequence at best position */
    out->len = N;
    for (uint32_t i = 0; i < best_p; i++)
        out->data[i] = ternary->data[i];
    out->data[best_p] = insert_val;
    for (uint32_t i = best_p; i < P; i++)
        out->data[i + 1] = ternary->data[i];

    if (best_pos) *best_pos = best_p;

    return 0;
}

/* ===================================================================== */
/* Hardcoded Patent Table 3 Sequences                                    */
/* ===================================================================== */

/*
 * From the patent's Table 3 (base ternary sequences with uniform
 * distribution of zero and non-zero elements):
 *
 * 3/8-OOK (length 8):  {0, 0, -1, 1, 1, 0, 1, 0}  (from example)
 * 4/16-OOK (length 16): constructed from degree-4 m-seq
 * 5/32-OOK (length 32): constructed from degree-5 m-seq
 *
 * The patent gives multiple variants; we store the primary one.
 */

/* 3/8-OOK: based on the perfect ternary sequence example in §604:
 * Λ(x,y) = {0, 0, -1, 1, 1, 0, 1} with "0" inserted → length 8 */
static const tseq_elem_t table3_8[] = {0, 0, 0, -1, 1, 1, 0, 1};

/* 4/16-OOK: constructed from degree-4 LFSR, complement m-seq family.
 * Selected for uniform distribution of zeros. */
static const tseq_elem_t table4_16[] = {
    0, -1, 0, 1, 1, 0, -1, 1, 0, 1, -1, 0, 1, 0, -1, 0
};

/* 5/32-OOK: from degree-5 m-seq, complement seed, minimum-MSAC sequence */
static const tseq_elem_t table5_32[] = {
    0,  1, 0, -1, 1, 0, 1, -1,  0, -1, 1, 0, 1, 0, -1, 1,
    0, -1, 0,  1, 0, 1, -1, 0, -1, 0,  1, -1, 0, 1,  0, 1
};

int tseq_get_table_sequence(uint32_t family_id, uint32_t variant,
                            tseq_seq_t *out)
{
    if (!out) return -1;
    (void)variant;  /* only one variant stored currently */

    switch (family_id) {
    case TSEQ_FAMILY_3_8:
        out->len = 8;
        memcpy(out->data, table3_8, 8 * sizeof(tseq_elem_t));
        return 0;
    case TSEQ_FAMILY_4_16:
        out->len = 16;
        memcpy(out->data, table4_16, 16 * sizeof(tseq_elem_t));
        return 0;
    case TSEQ_FAMILY_5_32:
        out->len = 32;
        memcpy(out->data, table5_32, 32 * sizeof(tseq_elem_t));
        return 0;
    default:
        return -1;
    }
}

/* ===================================================================== */
/* Codeset Construction                                                  */
/* ===================================================================== */

int tseq_build_codeset(const tseq_seq_t *base,
                       tseq_seq_t *codeset,
                       uint32_t max_n)
{
    if (!base || !codeset || base->len == 0) return -1;

    uint32_t N = base->len;
    if (N > max_n) return -1;

    for (uint32_t g = 0; g < N; g++)
        tseq_cyclic_shift(base, g, &codeset[g]);

    return (int)N;
}
