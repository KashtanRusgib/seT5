/**
 * @file samsung_tseq.h
 * @brief seT6 Ternary Sequence Engine — Samsung CN105745888A
 *
 * Core types and algorithms for Samsung's "Method and system using
 * ternary sequences for simultaneous transmission to coherent and
 * non-coherent receivers" as described in patent CN105745888A
 * (filed 2013-10-29, granted 2019-11-26, assigned to Samsung
 * Electronics Co., Ltd.).  KR102349122B1 is the granted Korean
 * family member.
 *
 * Key patent concepts:
 *
 *   1. Base ternary sequence: a sequence over {-1, 0, +1} with
 *      excellent autocorrelation on both the ternary alphabet AND
 *      its binary absolute-value projection {0, 1}.
 *
 *   2. Cyclic-shift modulation: each data symbol of k bits maps to
 *      one of N = 2^k cyclic shifts of the base sequence, yielding
 *      a codeset C = { L^g{tb} : g ∈ Z_N }.
 *
 *   3. Generation pipeline:
 *        a. Select seed = m-sequence or complement(m-sequence)
 *           of length P = N-1.
 *        b. If weight(seed) is a perfect square → generate perfect
 *           ternary sequence via preferred-pair cross-correlation.
 *        c. Else → generate near-perfect sequence by inverting
 *           non-zero positions and selecting minimum-MSAC candidate.
 *        d. Insert a predefined value ("0" if m-seq seed, "1" if
 *           complement) at the position minimising MSAC over both
 *           ternary and binary autocorrelation → base ternary seq.
 *
 *   4. OOK naming: 3/8-OOK (k=3, N=8), 4/16-OOK (k=4, N=16),
 *      5/32-OOK (k=5, N=32).
 *
 *   5. Detection at receiver: correlate received signal with all N
 *      cyclic shifts, pick max correlation → inverse-map to symbol.
 *      Coherent: correlate with ternary base shifts.
 *      Non-coherent: correlate with |base| shifts (binary envelope).
 *
 * Mapping to seT6:
 *   seT6 balanced ternary {-1, 0, +1} maps directly to the ternary
 *   alphabet of CN105745888A with no translation:
 *     TRIT_FALSE  (-1) = -1
 *     TRIT_UNKNOWN ( 0) =  0
 *     TRIT_TRUE   (+1) = +1
 *
 * @see samsung_tseq_modem.h  for modulation / demodulation API
 * @see samsung_tseq_mmio.h   for hardware register map
 * @see trit.h                for the core trit type
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_SAMSUNG_TSEQ_H
#define SET6_SAMSUNG_TSEQ_H

#include <stdint.h>
#include <stddef.h>
#include "set6/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Constants                                                             */
/* ===================================================================== */

/** Maximum supported base sequence length (5/32-OOK) */
#define TSEQ_MAX_LEN          64

/** Maximum symbol size in bits (k) */
#define TSEQ_MAX_K            6

/** Maximum number of cyclic shifts N = 2^k */
#define TSEQ_MAX_N            (1 << TSEQ_MAX_K)

/** Standard sequence families from the patent (Table 4) */
#define TSEQ_FAMILY_3_8       0   /* k=3, N=8,  3/8-OOK  */
#define TSEQ_FAMILY_4_16      1   /* k=4, N=16, 4/16-OOK */
#define TSEQ_FAMILY_5_32      2   /* k=5, N=32, 5/32-OOK */
#define TSEQ_FAMILY_COUNT     3

/* ===================================================================== */
/* Types                                                                 */
/* ===================================================================== */

/**
 * A ternary sequence element — alias for seT6 trit.
 * Values: -1, 0, +1 (matches CN105745888A alphabet exactly).
 */
typedef trit tseq_elem_t;

/**
 * A ternary sequence of bounded length.
 */
typedef struct {
    tseq_elem_t data[TSEQ_MAX_LEN];
    uint32_t    len;      /**< Active length of the sequence */
} tseq_seq_t;

/**
 * Seed type: m-sequence or complement of m-sequence.
 * Determines the predefined value inserted (0 or 1 respectively).
 */
typedef enum {
    TSEQ_SEED_MSEQ     = 0,  /**< m-sequence seed */
    TSEQ_SEED_COMP     = 1   /**< Complement of m-sequence */
} tseq_seed_type_t;

/**
 * Sequence quality classification.
 */
typedef enum {
    TSEQ_QUALITY_PERFECT      = 0,  /**< Weight is perfect square */
    TSEQ_QUALITY_NEAR_PERFECT = 1   /**< Weight is not perfect square */
} tseq_quality_t;

/**
 * OOK family descriptor — captures the patent's Table 4 naming.
 */
typedef struct {
    uint32_t       family_id;     /**< TSEQ_FAMILY_* constant       */
    uint32_t       k;             /**< Symbol size in bits           */
    uint32_t       N;             /**< Sequence length = 2^k         */
    tseq_seed_type_t seed_type;   /**< m-seq or complement           */
    tseq_quality_t quality;       /**< Perfect or near-perfect       */
    const char    *name;          /**< e.g. "3/8-OOK"               */
} tseq_family_t;

/**
 * Complete sequence generation state.
 */
typedef struct {
    tseq_seq_t      seed;         /**< Seed sequence (length N-1)    */
    tseq_seed_type_t seed_type;   /**< m-seq or complement           */
    tseq_quality_t  quality;      /**< Perfect / near-perfect        */
    tseq_seq_t      ternary;      /**< Generated ternary sequence    */
    tseq_seq_t      base;         /**< Final base ternary sequence   */
    uint32_t        insert_pos;   /**< Position where predefined val inserted */
    double          msac;         /**< MSAC of the base sequence     */
    double          msac_abs;     /**< MSAC of |base|                */
} tseq_gen_state_t;

/* ===================================================================== */
/* Inline Utilities                                                      */
/* ===================================================================== */

/** Absolute value of a trit (project {-1,0,+1} → {0,1}) */
static inline tseq_elem_t tseq_abs(tseq_elem_t v)
{
    return (tseq_elem_t)(v < 0 ? -v : v);
}

/** Weight of a sequence = number of non-zero elements (patent §501) */
static inline uint32_t tseq_weight(const tseq_seq_t *seq)
{
    uint32_t w = 0;
    for (uint32_t i = 0; i < seq->len; i++)
        if (seq->data[i] != 0) w++;
    return w;
}

/** Check if n is a perfect square (patent §502) */
static inline int tseq_is_perfect_square(uint32_t n)
{
    if (n == 0) return 1;
    uint32_t r = 1;
    while (r * r < n) r++;
    return (r * r == n);
}

/**
 * Cyclic shift: shift sequence left by 'g' positions (patent Eq. 2).
 * L^g{x}[i] = x[(i + g) mod N]
 */
static inline void tseq_cyclic_shift(const tseq_seq_t *src,
                                     uint32_t g,
                                     tseq_seq_t *dst)
{
    dst->len = src->len;
    uint32_t N = src->len;
    for (uint32_t i = 0; i < N; i++)
        dst->data[i] = src->data[(i + g) % N];
}

/**
 * Correlation of two ternary sequences (patent Eq. 6 / discrete form).
 * Corr(x, y) = Σ x[i] · y[i]
 */
static inline int32_t tseq_correlate(const tseq_seq_t *x,
                                     const tseq_seq_t *y)
{
    int32_t corr = 0;
    uint32_t len = (x->len < y->len) ? x->len : y->len;
    for (uint32_t i = 0; i < len; i++)
        corr += (int32_t)x->data[i] * (int32_t)y->data[i];
    return corr;
}

/**
 * Compute absolute-value projection of a sequence.
 * |c_g|[i] = |c_g[i]|   (patent Eq. 8)
 */
static inline void tseq_abs_project(const tseq_seq_t *src,
                                    tseq_seq_t *dst)
{
    dst->len = src->len;
    for (uint32_t i = 0; i < src->len; i++)
        dst->data[i] = tseq_abs(src->data[i]);
}

/* ===================================================================== */
/* Core API — implemented in samsung_tseq.c                              */
/* ===================================================================== */

/**
 * Get a predefined OOK family descriptor.
 * @param family_id One of TSEQ_FAMILY_3_8, TSEQ_FAMILY_4_16, TSEQ_FAMILY_5_32
 * @return Pointer to static family descriptor, or NULL if invalid.
 */
const tseq_family_t *tseq_get_family(uint32_t family_id);

/**
 * Generate an m-sequence of length P = 2^n - 1 using LFSR.
 * @param n     Degree (resulting length = 2^n - 1).
 * @param poly  Primitive polynomial in GF(2) as a bitmask.
 * @param out   Output sequence with elements {0, 1} in bipolar form {-1, +1}.
 * @return 0 on success, -1 on error.
 */
int tseq_gen_msequence(uint32_t n, uint32_t poly, tseq_seq_t *out);

/**
 * Compute the complement of an m-sequence.
 * Flips: +1 → -1, -1 → +1, 0 stays 0.
 * @param src  Source m-sequence.
 * @param dst  Output complemented sequence.
 */
void tseq_complement(const tseq_seq_t *src, tseq_seq_t *dst);

/**
 * Compute periodic cross-correlation θ(x,y) (patent Eq. 10).
 * @param x, y  Input sequences of length P.
 * @param out   Output correlation sequence of length P.
 * @return 0 on success.
 */
int tseq_cross_correlation(const tseq_seq_t *x, const tseq_seq_t *y,
                           tseq_seq_t *out);

/**
 * Generate a perfect ternary sequence from a seed m-sequence.
 * Uses preferred-pair cross-correlation (patent Fig. 6, steps 601-604).
 * @param seed  Seed m-sequence (length P = N-1).
 * @param decim Decimation index for preferred pair partner.
 * @param out   Output perfect ternary sequence of length P.
 * @return 0 on success, -1 if weight is not a perfect square.
 */
int tseq_gen_perfect(const tseq_seq_t *seed, uint32_t decim,
                     tseq_seq_t *out);

/**
 * Generate a near-perfect ternary sequence from a seed.
 * Inverts non-zero positions to minimise MSAC (patent Fig. 7).
 * @param seed     Seed sequence (m-seq or complement, length P).
 * @param ratio_lo Lower bound on (-1 count)/(+1 count) ratio.
 * @param ratio_hi Upper bound on ratio.
 * @param out      Output near-perfect ternary sequence.
 * @return 0 on success.
 */
int tseq_gen_near_perfect(const tseq_seq_t *seed,
                          double ratio_lo, double ratio_hi,
                          tseq_seq_t *out);

/**
 * Compute the Mean Square Autocorrelation Coefficient (patent Eq. 11-12).
 * @param seq  Input sequence.
 * @return MSAC value (lower is better).
 */
double tseq_msac(const tseq_seq_t *seq);

/**
 * Compute aperiodic autocorrelation R_a(k) (patent Eq. 14).
 * @param seq  Input sequence.
 * @param k    Delay.
 * @return Aperiodic autocorrelation at delay k.
 */
int32_t tseq_aperiodic_autocorr(const tseq_seq_t *seq, uint32_t k);

/**
 * Insert predefined value to form the base ternary sequence (patent §505).
 * Tries all positions and selects the one minimising MSAC over
 * both ternary and |ternary| sequences.
 * @param ternary   Input perfect/near-perfect ternary sequence (len P).
 * @param seed_type Determines inserted value: 0 for m-seq, 1 for complement.
 * @param out       Output base ternary sequence (length P + 1 = N).
 * @param best_pos  Output: position where value was inserted.
 * @return 0 on success.
 */
int tseq_gen_base(const tseq_seq_t *ternary,
                  tseq_seed_type_t seed_type,
                  tseq_seq_t *out,
                  uint32_t *best_pos);

/**
 * Retrieve a hardcoded base ternary sequence from patent Table 3.
 * @param family_id  TSEQ_FAMILY_3_8, _4_16, or _5_32.
 * @param variant    Variant index (0 = first listed in table).
 * @param out        Output base ternary sequence.
 * @return 0 on success, -1 if unknown family/variant.
 */
int tseq_get_table_sequence(uint32_t family_id, uint32_t variant,
                            tseq_seq_t *out);

/**
 * Build the full codeset C as all N cyclic shifts of a base sequence.
 * @param base     Base ternary sequence of length N.
 * @param codeset  Output array of N sequences.
 * @param max_n    Capacity of codeset array.
 * @return Number of sequences generated, or -1 on error.
 */
int tseq_build_codeset(const tseq_seq_t *base,
                       tseq_seq_t *codeset,
                       uint32_t max_n);

#ifdef __cplusplus
}
#endif

#endif /* SET6_SAMSUNG_TSEQ_H */
