/**
 * @file pam3_transcode.c
 * @brief seT5 PAM-3 Interconnect Compression — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/pam3_transcode.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

static int i_abs(int v) __attribute__((unused));
static int i_abs(int v) { return v < 0 ? -v : v; }

/** xorshift32 PRNG */
static uint32_t pam3_xorshift(uint32_t *seed) {
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/* ---- API -------------------------------------------------------------- */

void pam3_stats_init(pam3_stats_t *stats) {
    memset(stats, 0, sizeof(*stats));
}

int pam3_encode(pam3_frame_t *frame, const trit *trits, int count,
                pam3_stats_t *stats) {
    if (!frame || !trits || count <= 0 || count > PAM3_MAX_TRITS)
        return -1;

    memset(frame, 0, sizeof(*frame));
    frame->mode = PAM3_MODE_DIRECT;
    frame->count = count;

    for (int i = 0; i < count; i++) {
        pam3_symbol_t *sym = &frame->symbols[i];
        sym->trit_value = trits[i];

        switch (trits[i]) {
            case TRIT_TRUE:    sym->voltage_mv = PAM3_V_HIGH_MV; break;
            case TRIT_FALSE:   sym->voltage_mv = PAM3_V_LOW_MV;  break;
            default:           sym->voltage_mv = PAM3_V_MID_MV;  break;
        }
    }

    if (stats) {
        stats->symbols_sent   += count;
        stats->trits_encoded  += count;
        stats->bits_equivalent += (count * PAM3_BITS_PER_SYMBOL_X1000) / 1000;
        stats->bandwidth_gain_pct =
            ((PAM3_BITS_PER_SYMBOL_X1000 - NRZ_BITS_PER_SYMBOL_X1000) * 100)
            / NRZ_BITS_PER_SYMBOL_X1000;
    }

    return count;
}

int pam3_decode(trit *out, const pam3_frame_t *frame, pam3_stats_t *stats) {
    if (!out || !frame || frame->count <= 0)
        return -1;

    for (int i = 0; i < frame->count; i++) {
        int v = frame->symbols[i].voltage_mv;

        /* Threshold-based decoding */
        if (v > PAM3_V_HIGH_MV / 2)
            out[i] = TRIT_TRUE;
        else if (v < PAM3_V_LOW_MV / 2)
            out[i] = TRIT_FALSE;
        else
            out[i] = TRIT_UNKNOWN;
    }

    if (stats) {
        stats->trits_encoded += frame->count;
    }

    return frame->count;
}

int pam3_add_noise(pam3_frame_t *frame, int noise_mv, uint32_t seed) {
    if (!frame || noise_mv <= 0)
        return 0;

    uint32_t rng = seed;
    int corrupted = 0;

    for (int i = 0; i < frame->count; i++) {
        /* Generate signed noise: [-noise_mv, +noise_mv] */
        int n = (int)(pam3_xorshift(&rng) % (2 * (uint32_t)noise_mv + 1)) - noise_mv;
        frame->symbols[i].voltage_mv += n;

        /* Check if noise caused a state change */
        int v = frame->symbols[i].voltage_mv;
        trit decoded;
        if (v > PAM3_V_HIGH_MV / 2)
            decoded = TRIT_TRUE;
        else if (v < PAM3_V_LOW_MV / 2)
            decoded = TRIT_FALSE;
        else
            decoded = TRIT_UNKNOWN;

        if (decoded != frame->symbols[i].trit_value)
            corrupted++;
    }

    return corrupted;
}

void pam3_pre_emphasis(pam3_frame_t *frame, int boost_pct) {
    if (!frame || frame->count < 2 || boost_pct <= 0)
        return;

    for (int i = 1; i < frame->count; i++) {
        int prev = frame->symbols[i - 1].voltage_mv;
        int curr = frame->symbols[i].voltage_mv;

        /* Boost transition (different from previous) */
        if (curr != prev) {
            int delta = curr - prev;
            int boost = (delta * boost_pct) / 100;
            frame->symbols[i].voltage_mv += boost;
        }
    }
}

void pam3_eye_diagram(const pam3_frame_t *frame, int *height, int *margin) {
    if (!frame || frame->count < 2) {
        if (height) *height = 0;
        if (margin) *margin = 0;
        return;
    }

    /* Find min/max voltage to determine eye opening */
    int min_high = PAM3_V_HIGH_MV * 2;
    int max_low  = PAM3_V_LOW_MV * 2;

    for (int i = 0; i < frame->count; i++) {
        int v = frame->symbols[i].voltage_mv;
        trit t = frame->symbols[i].trit_value;

        if (t == TRIT_TRUE && v < min_high)
            min_high = v;
        if (t == TRIT_FALSE && v > max_low)
            max_low = v;
    }

    int eye_h = min_high - max_low;
    if (height) *height = eye_h;

    /* Margin = eye_height / (ideal eye height) × 100 */
    int ideal = PAM3_V_HIGH_MV - PAM3_V_LOW_MV;
    if (margin) *margin = (ideal > 0) ? (eye_h * 100) / ideal : 0;
}

int pam3_bandwidth_gain(int trit_count) {
    if (trit_count <= 0) return 0;
    /* PAM-3: 1.585 bits/sym vs NRZ 1 bit/sym = +58.5% → 585 (×10) */
    return (PAM3_BITS_PER_SYMBOL_X1000 - NRZ_BITS_PER_SYMBOL_X1000) * 1000
           / NRZ_BITS_PER_SYMBOL_X1000;
}

int pam3_trits_per_cycle(int lane_width_bits, int pam_level) {
    if (lane_width_bits <= 0 || pam_level < 3)
        return 0;

    /* For PAM-3: 1 trit per symbol, 1 symbol = 1 wire period */
    /* For PAM-4: can encode floor(log3(4)) = 1 trit per symbol via mapping */
    if (pam_level == 3)
        return lane_width_bits * 1000; /* 1 trit per bit (direct) */
    else
        return (lane_width_bits * 1000 * 2) / 3; /* rough PAM-4 mapping */
}

int pam3_encode_pam4(pam3_frame_t *frame, const trit *trits, int count) {
    if (!frame || !trits || count <= 0)
        return -1;

    memset(frame, 0, sizeof(*frame));
    frame->mode = PAM3_MODE_PAM4_INTEROP;

    /* Map pairs of trits to PAM-4 levels:
     * (-1,-1)→-300  (-1,0)→-100  (-1,+1)→+100
     * ( 0,-1)→-100  ( 0,0)→+100  ( 0,+1)→+300
     * (+1,-1)→+100  (+1,0)→+300  (+1,+1)→-300 (wrap)
     * This is a simplified demonstration mapping
     */
    int sym_count = 0;
    for (int i = 0; i + 1 < count && sym_count < PAM3_MAX_SYMBOLS; i += 2) {
        int t0 = (int)trits[i] + 1;     /* 0, 1, 2 */
        int t1 = (int)trits[i + 1] + 1; /* 0, 1, 2 */
        int combined = t0 * 3 + t1;      /* 0..8 */
        int level = combined % 4;         /* map to 0,1,2,3 */

        static const int pam4_voltages[4] = {
            PAM4_V0_MV, PAM4_V1_MV, PAM4_V2_MV, PAM4_V3_MV
        };

        frame->symbols[sym_count].voltage_mv = pam4_voltages[level];
        frame->symbols[sym_count].trit_value = trits[i]; /* store first trit as ref */
        sym_count++;
    }

    /* Handle odd trit */
    if (count % 2 == 1 && sym_count < PAM3_MAX_SYMBOLS) {
        pam3_symbol_t *sym = &frame->symbols[sym_count];
        sym->trit_value = trits[count - 1];
        sym->voltage_mv = (int)trits[count - 1] * PAM3_V_HIGH_MV;
        sym_count++;
    }

    frame->count = sym_count;
    return sym_count;
}

int pam3_decode_pam4(trit *out, const pam3_frame_t *frame) {
    if (!out || !frame)
        return -1;

    /* Simple: decode each PAM-4 symbol as a single trit based on voltage */
    int count = 0;
    for (int i = 0; i < frame->count && count < PAM3_MAX_TRITS; i++) {
        int v = frame->symbols[i].voltage_mv;
        if (v > 200)       out[count++] = TRIT_TRUE;
        else if (v < -200) out[count++] = TRIT_FALSE;
        else               out[count++] = TRIT_UNKNOWN;
    }

    return count;
}
