/**
 * @file pam3_transcode.h
 * @brief seT6 PAM-3/4 High-Radix Interconnect Compression
 *
 * Encodes balanced ternary data for Pulse Amplitude Modulation
 * (PAM-3) physical layer transmission. Maps trits to voltage
 * levels for chip-to-chip interconnect.
 *
 * Key features:
 *   - PAM-3 symbol mapping: {-1, 0, +1} → {-V, 0, +V}
 *   - PAM-4 interop: pack 2 trits per PAM-4 symbol
 *   - HBM (High Bandwidth Memory) channel packing
 *   - PCIe lane trit encoding
 *   - Bandwidth efficiency: ~58% more info per symbol vs binary
 *   - Eye diagram simulation for signal integrity
 *   - Pre-emphasis / de-emphasis for ISI mitigation
 *
 * Wire formats:
 *   PAM-3: 1 trit per symbol, 1.585 bits/symbol
 *   PAM-4: 2 trits per symbol (9 levels → 4-level mapping), 2 bits/symbol
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § High-Radix Interconnect Compression
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_PAM3_TRANSCODE_H
#define SET6_PAM3_TRANSCODE_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Maximum symbols per transmission frame */
#define PAM3_MAX_SYMBOLS    256

/** Maximum trits per frame */
#define PAM3_MAX_TRITS      256

/** PAM voltage levels (millivolts) */
#define PAM3_V_HIGH_MV      400
#define PAM3_V_MID_MV       0
#define PAM3_V_LOW_MV       (-400)

/** PAM-4 voltage levels */
#define PAM4_V3_MV          300
#define PAM4_V2_MV          100
#define PAM4_V1_MV          (-100)
#define PAM4_V0_MV          (-300)

/** Bandwidth comparison: bits per symbol */
#define PAM3_BITS_PER_SYMBOL_X1000  1585  /**< log2(3) × 1000 */
#define PAM4_BITS_PER_SYMBOL_X1000  2000  /**< log2(4) × 1000 */
#define NRZ_BITS_PER_SYMBOL_X1000   1000  /**< Binary NRZ */

/* ==== Structures ======================================================= */

/** PAM encoding mode */
typedef enum {
    PAM3_MODE_DIRECT,     /**< 1 trit per symbol (native PAM-3) */
    PAM3_MODE_PACKED,     /**< Pack multiple trits per symbol */
    PAM3_MODE_PAM4_INTEROP /**< Map trits to PAM-4 levels */
} pam3_mode_t;

/**
 * @brief PAM-3 symbol (voltage level representation).
 */
typedef struct {
    int  voltage_mv;       /**< Symbol voltage in millivolts */
    trit trit_value;       /**< Corresponding trit value */
} pam3_symbol_t;

/**
 * @brief PAM-3 transmission frame.
 */
typedef struct {
    pam3_symbol_t symbols[PAM3_MAX_SYMBOLS]; /**< Encoded symbols */
    int           count;                      /**< Number of symbols */
    pam3_mode_t   mode;                       /**< Encoding mode */
    int           preamble_len;               /**< Preamble symbols */
} pam3_frame_t;

/**
 * @brief Channel statistics.
 */
typedef struct {
    int   symbols_sent;        /**< Total symbols transmitted */
    int   trits_encoded;       /**< Total trits encoded */
    int   bits_equivalent;     /**< Equivalent binary bits */
    int   bandwidth_gain_pct;  /**< % gain over binary NRZ */
    int   eye_height_mv;       /**< Simulated eye diagram height */
    int   eye_margin_pct;      /**< Eye margin as % of height */
} pam3_stats_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize channel statistics.
 */
void pam3_stats_init(pam3_stats_t *stats);

/**
 * @brief Encode trits into PAM-3 frame.
 *
 * Each trit maps directly to a PAM-3 voltage level:
 *   +1 → +400mV, 0 → 0mV, -1 → -400mV
 *
 * @param frame  Output PAM-3 frame.
 * @param trits  Input trit array.
 * @param count  Number of trits.
 * @param stats  Optional stats tracker (may be NULL).
 * @return       Number of symbols generated.
 */
int pam3_encode(pam3_frame_t *frame, const trit *trits, int count,
                pam3_stats_t *stats);

/**
 * @brief Decode PAM-3 frame back to trits.
 *
 * @param out    Output trit array.
 * @param frame  Input PAM-3 frame.
 * @param stats  Optional stats tracker.
 * @return       Number of trits decoded.
 */
int pam3_decode(trit *out, const pam3_frame_t *frame, pam3_stats_t *stats);

/**
 * @brief Add channel noise to PAM-3 frame.
 *
 * Models ISI (inter-symbol interference) and random noise.
 *
 * @param frame     Frame to corrupt.
 * @param noise_mv  RMS noise amplitude (mV).
 * @param seed      PRNG seed.
 * @return          Number of symbols corrupted.
 */
int pam3_add_noise(pam3_frame_t *frame, int noise_mv, uint32_t seed);

/**
 * @brief Apply pre-emphasis to compensate for channel loss.
 *
 * Boosts transitions (different from previous symbol) by boost_pct%.
 *
 * @param frame     Frame to pre-emphasize.
 * @param boost_pct Boost percentage (10-50 typical).
 */
void pam3_pre_emphasis(pam3_frame_t *frame, int boost_pct);

/**
 * @brief Compute eye diagram metrics.
 *
 * @param frame   Frame to analyze.
 * @param height  Output: eye height (mV).
 * @param margin  Output: margin percentage.
 */
void pam3_eye_diagram(const pam3_frame_t *frame, int *height, int *margin);

/**
 * @brief Compute bandwidth efficiency vs binary NRZ.
 *
 * PAM-3 carries 1.585 bits/symbol vs NRZ 1 bit/symbol = +58.5%.
 *
 * @param trit_count  Number of trits.
 * @return            Bandwidth gain percentage (×10).
 */
int pam3_bandwidth_gain(int trit_count);

/**
 * @brief Compute trits per PCIe lane per clock cycle.
 *
 * At PAM-3: 1 trit/symbol × symbols/clock.
 *
 * @param lane_width_bits  Lane width in bits (e.g. 1 for PCIe).
 * @param pam_level        3 for PAM-3, 4 for PAM-4.
 * @return                 Trits per cycle (×1000).
 */
int pam3_trits_per_cycle(int lane_width_bits, int pam_level);

/**
 * @brief Encode trits for PAM-4 interop (2 trits → 1 PAM-4 symbol).
 *
 * Maps pairs of trits to 4-level PAM:
 *   (-1,-1)→V0, (-1,0)/(0,-1)→V1, (0,0)/(+1,-1)/(-1,+1)→V2, etc.
 *
 * @param frame  Output frame.
 * @param trits  Input trits (even count recommended).
 * @param count  Number of trits.
 * @return       Number of PAM-4 symbols.
 */
int pam3_encode_pam4(pam3_frame_t *frame, const trit *trits, int count);

/**
 * @brief Decode PAM-4 symbols back to trits.
 */
int pam3_decode_pam4(trit *out, const pam3_frame_t *frame);

#ifdef __cplusplus
}
#endif

#endif /* SET6_PAM3_TRANSCODE_H */
