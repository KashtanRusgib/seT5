/**
 * @file radix_transcode.h
 * @brief seT6 Radix-3 ↔ Radix-2 Transcoding Engine
 *
 * Low-latency conversion between balanced ternary and binary
 * representations, optimized for hybrid ternary/binary systems.
 *
 * Key features:
 *   - Single-value and batch transcoding
 *   - Lookup-table acceleration for small values
 *   - Packed trit ↔ byte stream encoding
 *   - Bandwidth efficiency metrics (trits vs bits)
 *   - HBM channel packing optimization
 *   - PCIe/DDR interleaving support
 *
 * Performance target: <3× overhead for radix boundary crossing.
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Radix-3 to Radix-2 Transcoding
 * @see multiradix.h RADIX_CONV instruction
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_RADIX_TRANSCODE_H
#define SET6_RADIX_TRANSCODE_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Maximum trits in a transcoded word */
#define RTC_MAX_TRITS       32

/** Maximum batch size for bulk transcoding */
#define RTC_MAX_BATCH       256

/** Bits per trit (information-theoretic: log2(3) ≈ 1.585) */
#define RTC_BITS_PER_TRIT_X1000  1585

/* ==== Structures ======================================================= */

/**
 * @brief Transcoding statistics.
 */
typedef struct {
    int   conversions;         /**< Total conversions performed */
    int   total_trits;         /**< Total trits processed */
    int   total_bits;          /**< Equivalent bits */
    int   lut_hits;            /**< LUT-accelerated conversions */
    int   bandwidth_ratio_x100;/**< Trit bandwidth advantage (×100) */
} rtc_stats_t;

/**
 * @brief Packed trit stream for wire transmission.
 *
 * Encodes trits in 2-bit packed format for binary wire protocols.
 * 16 trits per uint32_t word.
 */
typedef struct {
    uint32_t  words[RTC_MAX_TRITS / 16 + 1]; /**< Packed 2-bit trit words */
    int       trit_count;                      /**< Number of trits encoded */
} rtc_packed_stream_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize transcoding statistics.
 */
void rtc_stats_init(rtc_stats_t *stats);

/**
 * @brief Convert integer to balanced ternary trit array.
 *
 * Uses Avizienis signed-digit algorithm. LST at index 0.
 *
 * @param out    Output trit array (length >= width).
 * @param value  Integer to convert.
 * @param width  Number of trits to produce.
 * @param stats  Optional stats tracker (may be NULL).
 * @return       Number of non-zero trits.
 */
int rtc_int_to_ternary(trit *out, int value, int width, rtc_stats_t *stats);

/**
 * @brief Convert balanced ternary trit array to integer.
 *
 * Evaluates: result = Σ trit[i] × 3^i for i in [0, width).
 *
 * @param trits  Input trit array.
 * @param width  Number of trits to read.
 * @param stats  Optional stats tracker (may be NULL).
 * @return       Integer value.
 */
int rtc_ternary_to_int(const trit *trits, int width, rtc_stats_t *stats);

/**
 * @brief Batch convert integers to balanced ternary.
 *
 * @param out       Output trit arrays (batch × width).
 * @param values    Input integer array.
 * @param count     Number of values.
 * @param width     Trits per value.
 * @param stats     Optional stats tracker.
 * @return          0 on success.
 */
int rtc_batch_to_ternary(trit *out, const int *values, int count,
                         int width, rtc_stats_t *stats);

/**
 * @brief Batch convert balanced ternary to integers.
 *
 * @param out       Output integer array.
 * @param trits     Input trit arrays (count × width).
 * @param count     Number of values.
 * @param width     Trits per value.
 * @param stats     Optional stats tracker.
 * @return          0 on success.
 */
int rtc_batch_to_int(int *out, const trit *trits, int count,
                     int width, rtc_stats_t *stats);

/**
 * @brief Pack trit array into binary stream (2 bits per trit).
 *
 * Encoding: -1 → 0b10, 0 → 0b00, +1 → 0b01
 *
 * @param stream  Output packed stream.
 * @param trits   Input trit array.
 * @param count   Number of trits.
 * @return        Number of 32-bit words used.
 */
int rtc_pack(rtc_packed_stream_t *stream, const trit *trits, int count);

/**
 * @brief Unpack binary stream to trit array.
 *
 * @param out     Output trit array.
 * @param stream  Input packed stream.
 * @return        Number of trits unpacked.
 */
int rtc_unpack(trit *out, const rtc_packed_stream_t *stream);

/**
 * @brief Compute bandwidth efficiency ratio.
 *
 * Returns how many equivalent binary bits the ternary representation
 * carries vs. the binary wire bits consumed. Ideal = 1585/2000 = 79.25%.
 *
 * @param trit_count   Number of trits.
 * @return             Efficiency ratio × 1000.
 */
int rtc_bandwidth_efficiency(int trit_count);

/**
 * @brief Compute how many trits fit in a given number of binary bits.
 *
 * Optimal packing: floor(bits / log2(3)).
 *
 * @param bits   Available binary bits.
 * @return       Maximum trits that can be encoded.
 */
int rtc_trits_per_bits(int bits);

#ifdef __cplusplus
}
#endif

#endif /* SET6_RADIX_TRANSCODE_H */
