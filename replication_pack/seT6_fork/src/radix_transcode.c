/**
 * @file radix_transcode.c
 * @brief seT6 Radix Transcoding Engine — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/radix_transcode.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

static int i_abs(int v) { return v < 0 ? -v : v; }

/* Powers of 3 lookup (3^0 to 3^19) */
static const int pow3_table[20] __attribute__((unused)) = {
    1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683,
    59049, 177147, 531441, 1594323, 4782969, 14348907,
    43046721, 129140163, 387420489, 1162261467
};

/* ---- API -------------------------------------------------------------- */

void rtc_stats_init(rtc_stats_t *stats) {
    memset(stats, 0, sizeof(*stats));
}

int rtc_int_to_ternary(trit *out, int value, int width, rtc_stats_t *stats) {
    if (!out || width <= 0 || width > RTC_MAX_TRITS)
        return -1;

    int v = value;
    int nonzero = 0;

    for (int i = 0; i < width; i++) {
        int r = v % 3;
        if (r < 0) r += 3;

        if (r == 2) {
            out[i] = TRIT_FALSE;  /* -1 */
            v = (v + 1) / 3;
            nonzero++;
        } else if (r == 1) {
            out[i] = TRIT_TRUE;   /* +1 */
            v = (v - 1) / 3;
            nonzero++;
        } else {
            out[i] = TRIT_UNKNOWN; /* 0 */
            v = v / 3;
        }
    }

    if (stats) {
        stats->conversions++;
        stats->total_trits += width;
        stats->total_bits  += (width * RTC_BITS_PER_TRIT_X1000) / 1000;
        /* Check if value small enough for LUT */
        if (i_abs(value) <= 40) stats->lut_hits++;
    }

    return nonzero;
}

int rtc_ternary_to_int(const trit *trits, int width, rtc_stats_t *stats) {
    if (!trits || width <= 0) return 0;

    int result = 0;
    int w = (width > 20) ? 20 : width;  /* Prevent overflow */

    for (int i = w - 1; i >= 0; i--)
        result = result * 3 + (int)trits[i];

    if (stats) {
        stats->conversions++;
        stats->total_trits += width;
        stats->total_bits  += (width * RTC_BITS_PER_TRIT_X1000) / 1000;
    }

    return result;
}

int rtc_batch_to_ternary(trit *out, const int *values, int count,
                         int width, rtc_stats_t *stats) {
    if (!out || !values || count <= 0 || count > RTC_MAX_BATCH)
        return -1;

    for (int i = 0; i < count; i++)
        rtc_int_to_ternary(out + i * width, values[i], width, stats);

    if (stats) {
        int total_trits = count * width;
        int total_bits  = count * width * 2; /* 2-bit packed */
        if (total_bits > 0)
            stats->bandwidth_ratio_x100 = (total_trits * RTC_BITS_PER_TRIT_X1000) / (total_bits * 10);
    }

    return 0;
}

int rtc_batch_to_int(int *out, const trit *trits, int count,
                     int width, rtc_stats_t *stats) {
    if (!out || !trits || count <= 0)
        return -1;

    for (int i = 0; i < count; i++)
        out[i] = rtc_ternary_to_int(trits + i * width, width, stats);

    return 0;
}

int rtc_pack(rtc_packed_stream_t *stream, const trit *trits, int count) {
    if (!stream || !trits || count <= 0 || count > RTC_MAX_TRITS)
        return -1;

    memset(stream, 0, sizeof(*stream));
    stream->trit_count = count;

    for (int i = 0; i < count; i++) {
        /* Encoding: -1 → 0b10, 0 → 0b00, +1 → 0b01 */
        uint32_t enc;
        switch (trits[i]) {
            case TRIT_TRUE:    enc = 0x01; break;
            case TRIT_FALSE:   enc = 0x02; break;
            default:           enc = 0x00; break;
        }
        int word_idx = (i * 2) / 32;
        int bit_pos  = (i * 2) % 32;
        stream->words[word_idx] |= (enc << bit_pos);
    }

    return (count * 2 + 31) / 32;
}

int rtc_unpack(trit *out, const rtc_packed_stream_t *stream) {
    if (!out || !stream || stream->trit_count <= 0)
        return -1;

    static const trit decode[4] = { 0, 1, -1, 0 }; /* 00→0, 01→+1, 10→-1, 11→fault→0 */

    for (int i = 0; i < stream->trit_count; i++) {
        int word_idx = (i * 2) / 32;
        int bit_pos  = (i * 2) % 32;
        uint32_t enc = (stream->words[word_idx] >> bit_pos) & 0x03;
        out[i] = decode[enc];
    }

    return stream->trit_count;
}

int rtc_bandwidth_efficiency(int trit_count) {
    if (trit_count <= 0) return 0;
    /* Info bits = trit_count × log2(3) × 1000 */
    int info_bits_x1000 = trit_count * RTC_BITS_PER_TRIT_X1000;
    /* Wire bits = trit_count × 2 (2-bit encoding) × 1000 */
    int wire_bits_x1000 = trit_count * 2000;
    /* Efficiency = info / wire × 1000 */
    return (info_bits_x1000 * 1000) / wire_bits_x1000;
}

int rtc_trits_per_bits(int bits) {
    if (bits <= 0) return 0;
    /* trits = floor(bits × 1000 / 1585) */
    return (bits * 1000) / RTC_BITS_PER_TRIT_X1000;
}
