/**
 * @file trit_resisc.h
 * @brief seT6 ResISC — Residue-domain In-Sensor Computing for Edge AI
 *
 * Implements RNS-based bit-stream sensing/computing inspired by the
 * ResISC architecture (Residue-based In-Sensor Computing).  Sensor
 * pixels produce deterministic bit-streams encoding ternary pixel
 * values; RNS residue channels compute MAC operations directly in
 * the sensing path — eliminating separate ADC + MAC stages.
 *
 * Key features:
 *   - Bit-stream RNS encoding: pixel → deterministic bit-stream → residues
 *   - In-sensor MAC: per-channel modular accumulation
 *   - Energy model: sensor + compute combined (sub-pJ per MAC)
 *   - Noise-resilient: RNS redundancy detects bit-flip errors
 *   - Ternary-native: {-1, 0, +1} pixel values map directly to trits
 *
 * @see trit_rns.h      for RNS arithmetic core
 * @see trit_tmvm_rns.h  for TMVM+RNS integration
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_RESISC_H
#define SET6_TRIT_RESISC_H

#include "set5/trit.h"
#include "set5/trit_rns.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define RESISC_MAX_PIXELS        1024  /**< Max sensor array size          */
#define RESISC_MAX_WEIGHTS       256   /**< Max kernel weights             */
#define RESISC_BITSTREAM_LEN     32    /**< Bits per pixel bit-stream      */
#define RESISC_ENERGY_SENSE_FJ   50    /**< Femtojoules per pixel sense    */
#define RESISC_ENERGY_MAC_FJ     10    /**< Femtojoules per residue MAC    */
#define RESISC_ENERGY_ADC_FJ     200   /**< fJ saved by skipping ADC      */
#define RESISC_SNR_THRESHOLD_DB  20    /**< Minimum acceptable SNR (dB)    */

/* ==== Types ============================================================= */

/**
 * @brief Bit-stream encoded pixel value.
 *
 * A deterministic bit-stream of length RESISC_BITSTREAM_LEN encodes
 * a ternary pixel value.  The ratio of 1s to 0s determines the
 * effective analog value (stochastic analog of binary sigma-delta).
 */
typedef struct {
    uint32_t stream;         /**< Packed bit-stream (32 bits)         */
    int      trit_value;     /**< Decoded trit: {-1, 0, +1}          */
    int      ones_count;     /**< Number of 1-bits (determines level) */
} resisc_pixel_t;

/**
 * @brief ResISC sensor array state.
 */
typedef struct {
    int  initialized;

    /* RNS context for residue-domain computing */
    trit_rns_context_t  rns_ctx;

    /* Sensor pixel array */
    resisc_pixel_t  pixels[RESISC_MAX_PIXELS];
    int             pixel_count;

    /* Kernel weights (ternary) */
    trit            weights[RESISC_MAX_WEIGHTS];
    int             weight_count;

    /* Output: MAC result per output position */
    int             results[RESISC_MAX_PIXELS];
    int             result_count;

    /* RNS residue accumulator per output */
    trit_rns_t      rns_accum[RESISC_MAX_PIXELS];

    /* Energy and quality metrics */
    int64_t  energy_sense_fj;    /**< Total sensing energy (fJ)       */
    int64_t  energy_compute_fj;  /**< Total compute energy (fJ)       */
    int64_t  energy_saved_fj;    /**< Energy saved vs traditional ADC */
    int      snr_db;             /**< Estimated output SNR (dB)       */
    int      bit_errors;         /**< Detected bit-stream errors      */
} resisc_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize ResISC sensor array with an RNS context.
 * @param st   State to initialize.
 * @param ctx  Initialized RNS context.
 * @return 0 on success, -1 on error.
 */
int resisc_init(resisc_state_t *st, const trit_rns_context_t *ctx);

/**
 * @brief Encode a trit pixel array into bit-stream form.
 *
 * Each trit {-1, 0, +1} is encoded as a deterministic bit-stream:
 *   +1 → all 1s (0xFFFFFFFF),  0 → half 1s (0x55555555),
 *   -1 → all 0s (0x00000000).
 *
 * @param st      State.
 * @param pixels  Trit pixel values [count].
 * @param count   Number of pixels.
 * @return 0 on success, -1 on error.
 */
int resisc_encode_pixels(resisc_state_t *st, const trit *pixels, int count);

/**
 * @brief Load kernel weights for convolution.
 * @param st       State.
 * @param weights  Ternary weights [count].
 * @param count    Number of weights (kernel size).
 * @return 0 on success, -1 on error.
 */
int resisc_load_weights(resisc_state_t *st, const trit *weights, int count);

/**
 * @brief Execute in-sensor MAC using RNS bit-stream computing.
 *
 * Performs 1D convolution: for each output position i,
 *   result[i] = Σ_k pixels[i+k] * weights[k]
 * computed in the RNS residue domain.
 *
 * @param st  State (pixels + weights must be loaded).
 * @return 0 on success, -1 on error.
 */
int resisc_execute(resisc_state_t *st);

/**
 * @brief Get total energy consumed (sensing + compute) in femtojoules.
 * @param st  State after execution.
 * @return Total energy in fJ.
 */
int64_t resisc_get_energy(const resisc_state_t *st);

/**
 * @brief Get energy saved vs. traditional ADC+MAC pipeline.
 * @param st  State after execution.
 * @return Saved energy in fJ.
 */
int64_t resisc_get_energy_saved(const resisc_state_t *st);

/**
 * @brief Get estimated signal-to-noise ratio.
 * @param st  State after execution.
 * @return SNR in dB.
 */
int resisc_get_snr(const resisc_state_t *st);

/**
 * @brief Inject bit-stream noise and detect errors via RNS redundancy.
 *
 * Flips random bits in pixel bit-streams with probability @p error_rate,
 * then uses RNS redundancy to detect inconsistencies.
 *
 * @param st          State with encoded pixels.
 * @param error_rate  Bit flip probability [0.0, 1.0].
 * @return Number of detected errors, or -1 on failure.
 */
int resisc_inject_noise(resisc_state_t *st, double error_rate);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_RESISC_H */
