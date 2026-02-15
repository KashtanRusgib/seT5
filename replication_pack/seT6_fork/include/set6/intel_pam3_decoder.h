/**
 * @file intel_pam3_decoder.h
 * @brief Intel/Prodigy US11405248B2 — FPGA PAM-3 Decoder Pipeline Interface
 *
 * Software model of the Prodigy Technovations patent describing an FPGA-based
 * system for decoding PAM-3 (Pulse Amplitude Modulation, 3 levels) signals.
 *
 * The PAM-3 encoding maps directly to balanced ternary:
 *   Level +1  → TRIT_TRUE
 *   Level  0  → TRIT_UNKNOWN
 *   Level -1  → TRIT_FALSE
 *
 * Patent pipeline stages (fully modeled):
 *   1. ADC Interface — sampling & de-serialization
 *   2. DC Correction — time-domain averaging noise reduction
 *   3. Slope & Level Detection — threshold-based PAM-3 level decode
 *   4. Spike Filter — remove transient glitches
 *   5. Edge Detection — find transitions + "must transitions"
 *   6. Midpoint Detection — center of must-transitions
 *   7. First-Level Edge Filter — retain valid edges ≥ 9 samples
 *   8. Second-Level Edge Filter — discard edges near must-transitions
 *   9. Sampling Point Calculation — derive symbol timing
 *  10. Sampling Point Filter — eliminate erroneous sampling points
 *  11. PAM-3 Symbol Generation — output decoded symbols
 *
 * Integration with seT6:
 *   - Extends existing pam3_transcode.{h,c} with full decoder pipeline
 *   - Provides noise-tolerant decoding for ternary communication links
 *   - Compatible with T-Net (trit_net) and T-IPC subsystems
 *
 * The seT6 microkernel is NOT modified.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_INTEL_PAM3_DECODER_H
#define SET6_INTEL_PAM3_DECODER_H

#include "set6/trit.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==================================================================== */
/*  Constants (from patent specifications)                              */
/* ==================================================================== */

/** ADC oversampling ratio (12× per patent: 800Msps / 66.66Mbps) */
#define PAM3D_OVERSAMPLE_RATIO  12

/** Maximum number of raw ADC samples per decode session */
#define PAM3D_MAX_RAW_SAMPLES   4096

/** Maximum decoded PAM-3 symbols per session */
#define PAM3D_MAX_SYMBOLS       (PAM3D_MAX_RAW_SAMPLES / PAM3D_OVERSAMPLE_RATIO)

/** DC correction block length (per patent: 128 samples) */
#define PAM3D_DC_BLOCK_LEN      128

/** Must-transition window (per patent: within 12 samples) */
#define PAM3D_MUST_TRANS_WINDOW 12

/** Minimum edge distance for first-level filter (per patent: ≥9 samples) */
#define PAM3D_MIN_EDGE_DIST     9

/** Second-level filter lookahead (per patent: next 4 samples) */
#define PAM3D_EDGE_LOOKAHEAD    4

/** ADC resolution (8-bit, values 0-255) */
#define PAM3D_ADC_MAX           255

/* ==================================================================== */
/*  Threshold Configuration                                             */
/* ==================================================================== */

/**
 * @brief PAM-3 level decoding thresholds (per patent FIG. 4E).
 *
 * Four thresholds for slope-based level detection:
 *   plus_threshold:   sample > this → level = +1 (rising slope)
 *   minus_threshold:  sample < this → level = -1 (falling slope)
 *   zero_plus_threshold:  upper bound for level = 0 (falling slope)
 *   zero_minus_threshold: lower bound for level = 0 (rising slope)
 */
typedef struct {
    int plus_threshold;        /**< Default: 140 (0→+1 or -1→+1)   */
    int minus_threshold;       /**< Default: 95  (0→-1 or +1→-1)   */
    int zero_plus_threshold;   /**< Default: 160 (+1→0 threshold)   */
    int zero_minus_threshold;  /**< Default: 80  (-1→0 threshold)   */
    int dynamic_enabled;       /**< 1 = dynamically adjust thresholds */
} pam3d_thresholds_t;

/* ==================================================================== */
/*  DC Correction State                                                 */
/* ==================================================================== */

/**
 * @brief DC Correction module state.
 *
 * Per patent: uses time-domain averaging over a block of 128 samples
 * to compensate for signal level variations from the directional coupler.
 */
typedef struct {
    int  enabled;              /**< 1 = DC correction active           */
    int  plus_threshold;       /**< Upper threshold for correction     */
    int  minus_max_threshold;  /**< Lower threshold for correction     */
    int  block[PAM3D_DC_BLOCK_LEN]; /**< Circular buffer of samples   */
    int  block_pos;            /**< Current position in block          */
    int  block_count;          /**< Number of samples in block so far  */
    int  block_min;            /**< Running minimum in block           */
    int  block_max;            /**< Running maximum in block           */
} pam3d_dc_state_t;

/* ==================================================================== */
/*  Edge Information                                                    */
/* ==================================================================== */

/**
 * @brief Edge detection record.
 *
 * Edges are transitions in PAM-3 levels. "Must transitions" are
 * +1→-1 or -1→+1 transitions within 12 samples.
 */
typedef struct {
    int position;              /**< Sample index of edge               */
    int from_level;            /**< PAM-3 level before transition      */
    int to_level;              /**< PAM-3 level after transition       */
    int is_must_transition;    /**< 1 if +1↔-1 within 12 samples      */
    int midpoint;              /**< Midpoint of must-transition (0=invalid) */
    int retained;              /**< 1 if edge passes all filters       */
} pam3d_edge_t;

/** Maximum edges tracked per decode session */
#define PAM3D_MAX_EDGES         512

/* ==================================================================== */
/*  Decoder Pipeline State                                              */
/* ==================================================================== */

/**
 * @brief Complete PAM-3 decoder pipeline state.
 *
 * Encapsulates all 11 stages of the patent's FPGA processing pipeline.
 */
typedef struct {
    /* Configuration */
    pam3d_thresholds_t thresholds; /**< Level detection thresholds     */
    pam3d_dc_state_t   dc;        /**< DC correction state             */

    /* Stage 1: ADC raw samples (oversampled at 12×) */
    int  raw_samples[PAM3D_MAX_RAW_SAMPLES];
    int  raw_count;                /**< Number of raw samples           */

    /* Stage 2: DC-corrected samples */
    int  dc_corrected[PAM3D_MAX_RAW_SAMPLES];

    /* Stage 3: Decoded PAM-3 levels (before spike filter) */
    int  pam3_levels[PAM3D_MAX_RAW_SAMPLES];

    /* Stage 4: Spike-filtered PAM-3 levels */
    int  filtered_levels[PAM3D_MAX_RAW_SAMPLES];

    /* Stage 5-6: Edge detection with must-transition info */
    pam3d_edge_t edges[PAM3D_MAX_EDGES];
    int          edge_count;

    /* Stage 9-10: Sampling points */
    int  sampling_points[PAM3D_MAX_SYMBOLS];
    int  sampling_count;

    /* Stage 11: Decoded PAM-3 symbols (final output) */
    trit decoded_symbols[PAM3D_MAX_SYMBOLS];
    int  symbol_count;

    /* Statistics */
    int  total_samples_processed;
    int  total_symbols_decoded;
    int  spikes_filtered;
    int  edges_detected;
    int  must_transitions_found;
    int  erroneous_edges_removed;
    int  erroneous_sp_removed;

    int  initialized;
} pam3d_decoder_t;

/* ==================================================================== */
/*  API — Initialization                                                */
/* ==================================================================== */

/**
 * @brief Initialize the PAM-3 decoder pipeline with default thresholds.
 */
int pam3d_init(pam3d_decoder_t *dec);

/**
 * @brief Set custom thresholds for level detection.
 */
int pam3d_set_thresholds(pam3d_decoder_t *dec, const pam3d_thresholds_t *thr);

/**
 * @brief Enable or disable DC correction.
 */
int pam3d_set_dc_correction(pam3d_decoder_t *dec, int enabled);

/* ==================================================================== */
/*  API — Pipeline Stages (can be called individually or via decode())  */
/* ==================================================================== */

/**
 * @brief Stage 1: Load raw ADC samples into the decoder.
 *
 * Samples are 8-bit unsigned values (0-255) representing the
 * oversampled PAM-3 signal.
 */
int pam3d_load_samples(pam3d_decoder_t *dec, const int *samples, int count);

/**
 * @brief Stage 2: Apply DC correction to loaded samples.
 *
 * Uses time-domain averaging per patent (block length 128).
 * Formula: If MAX > plus_threshold AND MIN < minus_max_threshold:
 *   corrected = sample - MIN + minus_threshold
 * Else: corrected = sample (no correction)
 */
int pam3d_apply_dc_correction(pam3d_decoder_t *dec);

/**
 * @brief Stage 3: Slope and level detection.
 *
 * Decodes PAM-3 levels based on four thresholds and signal slope.
 */
int pam3d_detect_levels(pam3d_decoder_t *dec);

/**
 * @brief Stage 4: Spike filter.
 *
 * Removes transient glitches in decoded levels.
 */
int pam3d_spike_filter(pam3d_decoder_t *dec);

/**
 * @brief Stage 5: Edge detection.
 *
 * Detects all transitions and identifies "must transitions"
 * (+1↔-1 within 12 samples).
 */
int pam3d_detect_edges(pam3d_decoder_t *dec);

/**
 * @brief Stage 6: Midpoint detection for must-transitions.
 */
int pam3d_detect_midpoints(pam3d_decoder_t *dec);

/**
 * @brief Stage 7-8: First and second level edge filtering.
 */
int pam3d_filter_edges(pam3d_decoder_t *dec);

/**
 * @brief Stage 9-10: Sampling point calculation and filtering.
 */
int pam3d_calculate_sampling_points(pam3d_decoder_t *dec);

/**
 * @brief Stage 11: Generate final PAM-3 symbols from filtered levels.
 */
int pam3d_generate_symbols(pam3d_decoder_t *dec);

/* ==================================================================== */
/*  API — Full Pipeline Decode                                          */
/* ==================================================================== */

/**
 * @brief Run the complete 11-stage decode pipeline on loaded samples.
 *
 * Equivalent to calling all pipeline stages in sequence.
 *
 * @param dec   Initialized decoder
 * @return Number of decoded symbols, or -1 on error
 */
int pam3d_decode_full(pam3d_decoder_t *dec);

/**
 * @brief Get decoded symbols as trit array.
 *
 * @param dec   Decoder with completed decode
 * @param out   Output trit array
 * @param max   Maximum symbols to copy
 * @return Number of symbols copied
 */
int pam3d_get_symbols(const pam3d_decoder_t *dec, trit *out, int max);

/**
 * @brief Generate synthetic PAM-3 test signal.
 *
 * Creates an oversampled signal from a sequence of trit values,
 * optionally with noise injection for testing.
 *
 * @param trits      Input trit sequence
 * @param trit_count Number of trits
 * @param out        Output sample buffer (12× oversampled)
 * @param max_out    Maximum output samples
 * @param noise_seed If non-zero, adds random noise (seed for PRNG)
 * @return Number of generated samples, or -1 on error
 */
int pam3d_generate_test_signal(const trit *trits, int trit_count,
                               int *out, int max_out, uint32_t noise_seed);

#ifdef __cplusplus
}
#endif

#endif /* SET6_INTEL_PAM3_DECODER_H */
