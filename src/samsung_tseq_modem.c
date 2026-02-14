/**
 * @file samsung_tseq_modem.c
 * @brief Ternary Sequence Modem — Samsung CN105745888A
 *
 * Implements modulation (TX) and demodulation (RX) using cyclic-shift
 * encoding of ternary sequences per CN105745888A.
 *
 * TX: symbol → cyclic shift → base-sequence lookup → transmit.
 * RX: receive → correlate all shifts → argmax → inverse-map → symbol.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/samsung_tseq_modem.h"
#include "set5/samsung_tseq_mmio.h"
#include <string.h>
#include <math.h>

/* ===================================================================== */
/* Modem Initialisation                                                  */
/* ===================================================================== */

int tseq_modem_init(tseq_modem_t *modem,
                    uint32_t family_id,
                    tseq_rx_type_t rx_type,
                    tseq_map_type_t map_type)
{
    if (!modem) return -1;

    const tseq_family_t *fam = tseq_get_family(family_id);
    if (!fam) return -1;

    memset(modem, 0, sizeof(*modem));

    /* Load base sequence from patent Table 3 */
    tseq_seq_t base;
    if (tseq_get_table_sequence(family_id, 0, &base) != 0)
        return -1;

    return tseq_modem_init_custom(modem, &base, fam->k, rx_type, map_type);
}

int tseq_modem_init_custom(tseq_modem_t *modem,
                           const tseq_seq_t *base,
                           uint32_t k,
                           tseq_rx_type_t rx_type,
                           tseq_map_type_t map_type)
{
    if (!modem || !base) return -1;

    uint32_t N = 1U << k;
    if (N > TSEQ_MAX_N || base->len != N) return -1;

    memset(modem, 0, sizeof(*modem));

    /* TX config */
    modem->tx.k = k;
    modem->tx.N = N;
    modem->tx.map_type = map_type;
    memcpy(&modem->tx.base, base, sizeof(tseq_seq_t));

    /* Build TX codeset: all N cyclic shifts of base */
    tseq_build_codeset(base, modem->tx.codeset, TSEQ_MAX_N);

    /* RX config */
    modem->rx.k = k;
    modem->rx.N = N;
    modem->rx.rx_type = rx_type;
    modem->rx.map_type = map_type;
    memcpy(&modem->rx.base, base, sizeof(tseq_seq_t));

    /* Build RX reference set */
    if (rx_type == TSEQ_RX_COHERENT) {
        /* Coherent: correlate with ternary cyclic shifts (patent §304) */
        tseq_build_codeset(base, modem->rx.ref_set, TSEQ_MAX_N);
    } else {
        /* Non-coherent: correlate with |base| cyclic shifts (patent §304) */
        tseq_seq_t abs_base;
        tseq_abs_project(base, &abs_base);
        tseq_build_codeset(&abs_base, modem->rx.ref_set, TSEQ_MAX_N);
    }

    modem->initialised = 1;
    modem->family_id = TSEQ_FAMILY_COUNT; /* custom */

    return 0;
}

void tseq_modem_shutdown(tseq_modem_t *modem)
{
    if (!modem) return;
    memset(modem, 0, sizeof(*modem));
}

/* ===================================================================== */
/* Modulation (TX)                                                       */
/* ===================================================================== */

int tseq_modulate(const tseq_modem_t *modem,
                  uint32_t symbol,
                  tseq_seq_t *out)
{
    if (!modem || !modem->initialised || !out) return -1;
    if (symbol >= modem->tx.N) return -1;

    /* Step 1: map symbol to cyclic shift g (patent Eq. 3) */
    uint32_t g = tseq_symbol_to_shift(symbol, modem->tx.map_type);
    if (g >= modem->tx.N) return -1;

    /* Step 2: look up c_g from precomputed codeset */
    memcpy(out, &modem->tx.codeset[g], sizeof(tseq_seq_t));

    return 0;
}

int tseq_modulate_frame(const tseq_modem_t *modem,
                        const uint8_t *data,
                        size_t data_len,
                        tseq_frame_t *frame)
{
    if (!modem || !modem->initialised || !data || !frame) return -1;

    uint32_t k = modem->tx.k;
    uint32_t total_bits = (uint32_t)(data_len * 8);
    uint32_t num_symbols = total_bits / k;

    if (num_symbols > TSEQ_MAX_FRAME_SYMBOLS) num_symbols = TSEQ_MAX_FRAME_SYMBOLS;

    frame->k = k;
    frame->num_symbols = num_symbols;

    /* Extract k-bit symbols from byte stream */
    uint32_t bit_pos = 0;
    for (uint32_t s = 0; s < num_symbols; s++) {
        uint32_t symbol = 0;
        for (uint32_t b = 0; b < k; b++) {
            uint32_t byte_idx = bit_pos / 8;
            uint32_t bit_idx = 7 - (bit_pos % 8);
            if (byte_idx < data_len) {
                symbol |= ((data[byte_idx] >> bit_idx) & 1) << (k - 1 - b);
            }
            bit_pos++;
        }

        if (tseq_modulate(modem, symbol, &frame->sequences[s]) != 0)
            return -1;
    }

    return (int)num_symbols;
}

/* ===================================================================== */
/* Demodulation (RX)                                                     */
/* ===================================================================== */

int tseq_demodulate(const tseq_modem_t *modem,
                    const tseq_seq_t *received,
                    tseq_demod_result_t *result)
{
    if (!modem || !modem->initialised || !received || !result) return -1;

    uint32_t N = modem->rx.N;
    int32_t max_corr = -999999;
    uint32_t best_g = 0;

    /* Correlate received signal with all N reference sequences
     * (patent Eq. 6 for coherent, Eq. 7 for non-coherent) */
    for (uint32_t g = 0; g < N; g++) {
        int32_t corr;

        if (modem->rx.rx_type == TSEQ_RX_NON_COHERENT) {
            /* Non-coherent: correlate with |received| and |base| shifts */
            tseq_seq_t abs_received;
            tseq_abs_project(received, &abs_received);
            corr = tseq_correlate(&abs_received, &modem->rx.ref_set[g]);
        } else {
            /* Coherent: direct correlation */
            corr = tseq_correlate(received, &modem->rx.ref_set[g]);
        }

        result->all_corr[g].shift = g;
        result->all_corr[g].corr_value = corr;

        if (corr > max_corr) {
            max_corr = corr;
            best_g = g;
        }
    }

    result->best_shift = best_g;
    result->max_corr = max_corr;

    /* Inverse mapping: g_est → symbol (patent Eq. 4) */
    result->symbol = tseq_shift_to_symbol(best_g, modem->rx.map_type);

    return 0;
}

int tseq_demodulate_frame(const tseq_modem_t *modem,
                          const tseq_frame_t *frame,
                          uint32_t *symbols_out,
                          uint32_t max_symbols)
{
    if (!modem || !modem->initialised || !frame || !symbols_out)
        return -1;

    uint32_t count = frame->num_symbols;
    if (count > max_symbols) count = max_symbols;

    tseq_demod_result_t result;

    for (uint32_t s = 0; s < count; s++) {
        if (tseq_demodulate(modem, &frame->sequences[s], &result) != 0)
            return -1;
        symbols_out[s] = result.symbol;
    }

    return (int)count;
}

/* ===================================================================== */
/* SNR Estimation                                                        */
/* ===================================================================== */

double tseq_estimate_snr(const tseq_demod_result_t *result, uint32_t N)
{
    if (!result || N < 2) return 0.0;

    int32_t max_val = result->max_corr;
    double noise_sum = 0.0;
    uint32_t noise_count = 0;

    for (uint32_t g = 0; g < N; g++) {
        if (g == result->best_shift) continue;
        double v = (double)result->all_corr[g].corr_value;
        noise_sum += v * v;
        noise_count++;
    }

    if (noise_count == 0 || noise_sum == 0.0) return 100.0;

    double noise_mean = noise_sum / (double)noise_count;
    double snr_linear = ((double)max_val * (double)max_val) / noise_mean;

    /* Convert to dB */
    return 10.0 * log10(snr_linear + 1e-10);
}

/* ===================================================================== */
/* Noise Injection (for testing)                                         */
/* ===================================================================== */

void tseq_add_noise(tseq_seq_t *seq, double error_p, uint32_t seed)
{
    if (!seq || error_p <= 0.0) return;

    uint32_t state = seed ? seed : 0xDEADBEEF;

    for (uint32_t i = 0; i < seq->len; i++) {
        /* Simple xorshift32 PRNG */
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;

        double r = (double)(state & 0xFFFF) / 65536.0;
        if (r < error_p) {
            /* Flip to a different value */
            tseq_elem_t old = seq->data[i];
            if (old == 0) {
                seq->data[i] = (state & 0x10000) ? (tseq_elem_t)1
                                                  : (tseq_elem_t)-1;
            } else if (old == 1) {
                seq->data[i] = (state & 0x10000) ? (tseq_elem_t)0
                                                  : (tseq_elem_t)-1;
            } else {
                seq->data[i] = (state & 0x10000) ? (tseq_elem_t)0
                                                  : (tseq_elem_t)1;
            }
        }
    }
}
