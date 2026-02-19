/**
 * @file trit_stabilize.h
 * @brief seT6 Trit Stability Engine — inline implementation for tests.
 *
 * PVT corner sweeps, thermal/flicker/shot noise injection,
 * cosmic-ray SEU simulation, meta-stable detection, CNTFET drift.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_STABILIZE_H
#define TRIT_STABILIZE_H

#include <string.h>
#include <stdint.h>
#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

#define TSTAB_NOISE_THERMAL   0x01
#define TSTAB_NOISE_FLICKER   0x02
#define TSTAB_NOISE_SHOT      0x04
#define TSTAB_NOISE_ALL       0x07

#define TSTAB_CORNER_SLOW     0
#define TSTAB_CORNER_TYPICAL  1
#define TSTAB_CORNER_FAST     2

#define TSTAB_MAX_PVT_CONFIGS 27

/* ==== Types ============================================================ */

typedef struct {
    int process_corner;        /**< TSTAB_CORNER_SLOW / TYPICAL / FAST */
    int voltage_mv;            /**< Supply voltage in millivolts       */
    int temp_mk;               /**< Temperature in millikelvin         */
} tstab_pvt_config_t;

typedef struct {
    trit output_trit;          /**< Trit value after PVT + noise       */
    int  noise_margin_mv;      /**< Remaining noise margin (mV)        */
    int  flipped;              /**< 1 if the trit changed value        */
} tstab_pvt_result_t;

typedef struct {
    /* Noise model */
    int      noise_types;      /**< Bitmask of TSTAB_NOISE_* */
    int      noise_amplitude;  /**< Peak noise amplitude (mV) */
    unsigned noise_seed;       /**< PRNG seed for deterministic replay */

    /* PVT sweep */
    tstab_pvt_config_t pvt_configs[TSTAB_MAX_PVT_CONFIGS];
    int      pvt_count;        /**< Number of PVT configs generated */

    /* Statistics */
    int      total_tests;      /**< Total individual trit tests run */
    int      flips;            /**< Trit flips detected */
    int      stability_ppm;    /**< Flip rate in parts-per-million */
    int      worst_snm;        /**< Worst (min) noise margin seen (mV) */

    /* SEU (cosmic ray) model */
    int      seu_probability;  /**< SEU probability in PPM */
    int      seu_injected;     /**< Total SEU flips injected */
    int      seu_recovered;    /**< Total SEU flips recovered */
} tstab_state_t;

/* ==== Internal PRNG ==================================================== */

static inline unsigned tstab__prng(unsigned *seed) {
    *seed = *seed * 1103515245u + 12345u;
    return *seed;
}

/* ==== API ============================================================== */

/**
 * @brief Initialize the stability engine.  Zeroes all fields.
 * @return 0 on success, -1 if st is NULL.
 */
static inline int tstab_init(tstab_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    return 0;
}

/**
 * @brief Configure noise injection model.
 * @return 0 on success, -1 if st is NULL or amplitude < 0.
 */
static inline int tstab_configure_noise(tstab_state_t *st, int noise_types,
                                        int amplitude, unsigned seed) {
    if (!st || amplitude < 0) return -1;
    st->noise_types     = noise_types;
    st->noise_amplitude = amplitude;
    st->noise_seed      = seed;
    return 0;
}

/**
 * @brief Generate all 27 PVT corner configurations (3×3×3).
 *
 * Corners : {SLOW, TYPICAL, FAST}
 * Voltages: {700, 800, 900} mV
 * Temps   : {233000, 298000, 358000} mK  (-40 °C, 25 °C, 85 °C)
 *
 * pvt_configs[0]  = (SLOW,  700, 233000)
 * pvt_configs[26] = (FAST,  900, 358000)
 *
 * @return 27 (number of configs).
 */
static inline int tstab_generate_pvt_sweep(tstab_state_t *st) {
    if (!st) return -1;
    static const int corners[]  = { TSTAB_CORNER_SLOW,
                                    TSTAB_CORNER_TYPICAL,
                                    TSTAB_CORNER_FAST };
    static const int voltages[] = { 700, 800, 900 };
    static const int temps[]    = { 233000, 298000, 358000 };
    int idx = 0;
    for (int c = 0; c < 3; c++)
        for (int v = 0; v < 3; v++)
            for (int t = 0; t < 3; t++) {
                st->pvt_configs[idx].process_corner = corners[c];
                st->pvt_configs[idx].voltage_mv     = voltages[v];
                st->pvt_configs[idx].temp_mk        = temps[t];
                idx++;
            }
    st->pvt_count = 27;
    return 27;
}

/**
 * @brief Test a single trit value under one PVT configuration.
 *
 * Noise margin model:
 *   TRIT_TRUE  (+1) or TRIT_FALSE (-1):  margin = voltage_mv - 500
 *   TRIT_UNKNOWN (0):                    margin = voltage_mv / 2
 *
 * A pseudo-random noise perturbation is generated from the seed.
 * If that perturbation >= margin the trit flips.
 *
 * @return 0 on success.
 */
static inline int tstab_test_trit_pvt(tstab_state_t *st, trit input,
                                      const tstab_pvt_config_t *cfg,
                                      tstab_pvt_result_t *result) {
    if (!st || !cfg || !result) return -1;

    int margin;
    if (input == TRIT_UNKNOWN)
        margin = cfg->voltage_mv / 2;
    else
        margin = cfg->voltage_mv - 500;

    int noise = 0;
    if (st->noise_amplitude > 0)
        noise = (int)(tstab__prng(&st->noise_seed) %
                      (unsigned)st->noise_amplitude);

    result->output_trit    = input;
    result->noise_margin_mv = margin;
    result->flipped        = 0;

    if (margin > 0 && noise >= margin) {
        if (input == TRIT_TRUE)        result->output_trit = TRIT_FALSE;
        else if (input == TRIT_FALSE)  result->output_trit = TRIT_TRUE;
        else                           result->output_trit = TRIT_TRUE;
        result->flipped = 1;
    }

    st->total_tests++;
    if (st->total_tests == 1 || margin < st->worst_snm)
        st->worst_snm = margin;

    return 0;
}

/**
 * @brief Run a full PVT sweep: 3 trit values × 27 configs = 81 tests.
 * @return Number of trit flips detected.  Updates st->flips.
 */
static inline int tstab_run_full_sweep(tstab_state_t *st) {
    if (!st) return -1;
    static const trit values[] = { TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE };
    int sweep_flips = 0;
    for (int i = 0; i < st->pvt_count; i++) {
        for (int v = 0; v < 3; v++) {
            tstab_pvt_result_t res;
            tstab_test_trit_pvt(st, values[v], &st->pvt_configs[i], &res);
            if (res.flipped) sweep_flips++;
        }
    }
    st->flips = sweep_flips;
    return sweep_flips;
}

/**
 * @brief Compute flip rate in parts-per-million.
 *        = flips * 1000000 / total_tests   (0 when flips == 0).
 */
static inline int tstab_get_stability_ppm(tstab_state_t *st) {
    if (!st) return -1;
    int div = st->total_tests > 0 ? st->total_tests : 1;
    st->stability_ppm = st->flips * 1000000 / div;
    return st->stability_ppm;
}

/**
 * @brief Return the worst (minimum) noise margin observed across all tests.
 */
static inline int tstab_get_worst_snm(tstab_state_t *st) {
    if (!st) return -1;
    return st->worst_snm;
}

/* ==== SEU (Single-Event Upset) ========================================= */

/**
 * @brief Configure SEU probability.
 * @param probability_ppm  Probability in parts-per-million (0–1000000).
 * @return 0.
 */
static inline int tstab_configure_seu(tstab_state_t *st, int probability_ppm) {
    if (!st) return -1;
    st->seu_probability = probability_ppm;
    return 0;
}

/**
 * @brief Inject SEU flips into a trit array.
 *
 * For each trit, for each iteration, a PRNG roll decides whether to flip.
 * Probability is controlled by st->seu_probability (PPM).
 *
 * @return Number of flips injected.  Updates st->seu_injected.
 */
static inline int tstab_inject_seu(tstab_state_t *st, trit *trits,
                                   int count, int iterations) {
    if (!st || !trits) return -1;
    unsigned seed = st->noise_seed;
    int flips = 0;
    for (int iter = 0; iter < iterations; iter++) {
        for (int i = 0; i < count; i++) {
            unsigned r = tstab__prng(&seed) % 1000000u;
            if ((int)r < st->seu_probability) {
                /* Flip: TRUE↔FALSE, UNKNOWN→TRUE */
                if (trits[i] == TRIT_TRUE)        trits[i] = TRIT_FALSE;
                else if (trits[i] == TRIT_FALSE)   trits[i] = TRIT_TRUE;
                else                                trits[i] = TRIT_TRUE;
                flips++;
            }
        }
    }
    st->noise_seed = seed;
    st->seu_injected += flips;
    return flips;
}

/**
 * @brief Recover SEU-flipped trits by comparing against a known-good original.
 * @return Number of trits restored.  Updates st->seu_recovered.
 */
static inline int tstab_recover_seu(tstab_state_t *st, trit *trits,
                                    const trit *orig, int count) {
    if (!st || !trits || !orig) return -1;
    int recovered = 0;
    for (int i = 0; i < count; i++) {
        if (trits[i] != orig[i]) {
            trits[i] = orig[i];
            recovered++;
        }
    }
    st->seu_recovered += recovered;
    return recovered;
}

/* ==== Meta-Stability Detection ========================================= */

/**
 * @brief Detect metastable readings in a voltage array.
 *
 * A reading is metastable if its voltage falls in the uncertainty zone
 * (300 mV – 500 mV inclusive).
 *
 * @return Number of metastable readings, or -1 if voltages is NULL.
 */
static inline int tstab_detect_metastable(tstab_state_t *st,
                                          const int *voltages, int count) {
    if (!st || !voltages) return -1;
    int meta = 0;
    for (int i = 0; i < count; i++) {
        if (voltages[i] >= 300 && voltages[i] <= 500)
            meta++;
    }
    return meta;
}

/* ==== CNTFET Drift Integration ========================================= */

/**
 * @brief Incorporate CNTFET device drift as additional noise.
 *
 * Adds drift_mv to noise_amplitude.
 *
 * @return New total noise amplitude, or -1 if st is NULL.
 */
static inline int tstab_apply_cntfet_drift(tstab_state_t *st, int drift_mv) {
    if (!st) return -1;
    st->noise_amplitude += drift_mv;
    return st->noise_amplitude;
}

#ifdef __cplusplus
}
#endif

#endif /* TRIT_STABILIZE_H */
