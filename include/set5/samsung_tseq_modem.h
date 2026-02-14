/**
 * @file samsung_tseq_modem.h
 * @brief seT5 Ternary Sequence Modem — Samsung CN105745888A
 *
 * Modulation and demodulation layer implementing the cyclic-shift
 * transmission protocol from CN105745888A.
 *
 * Transmitter pipeline (patent Fig. 3, Fig. 8):
 *   1. Data → divide into k-bit symbols
 *   2. Symbol s_m → cyclic shift g = f(s_m) via one-to-one mapping
 *   3. Obtain ternary sequence c_g = L^g{tb}
 *   4. Transmit c_g
 *
 * Receiver pipeline (patent Fig. 10):
 *   1. Receive signal (corrupted by AWGN / channel impairments)
 *   2. Correlate with all N cyclic shifts of base sequence:
 *        Coherent:     Corr_g = Σ y[i]·c_g[i]     (patent Eq. 6)
 *        Non-coherent: Corr_g = Σ y[i]·|c_g[i]|   (patent Eq. 7)
 *   3. g_est = argmax(Corr_g)
 *   4. s_est = f^{-1}(g_est)                       (patent Eq. 4)
 *
 * @see samsung_tseq.h      for base-sequence generation
 * @see samsung_tseq_mmio.h  for hardware register map
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SAMSUNG_TSEQ_MODEM_H
#define SET5_SAMSUNG_TSEQ_MODEM_H

#include <stdint.h>
#include <stddef.h>
#include "set5/samsung_tseq.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Constants                                                             */
/* ===================================================================== */

/** Maximum number of symbols in a single transmission frame */
#define TSEQ_MAX_FRAME_SYMBOLS  256

/** Maximum data length in bytes for a frame */
#define TSEQ_MAX_FRAME_BYTES    ((TSEQ_MAX_FRAME_SYMBOLS * TSEQ_MAX_K) / 8)

/* ===================================================================== */
/* Types                                                                 */
/* ===================================================================== */

/**
 * Receiver type — determines demodulation strategy (patent §304).
 */
typedef enum {
    TSEQ_RX_COHERENT     = 0,  /**< Uses phase info, ternary alphabet  */
    TSEQ_RX_NON_COHERENT = 1   /**< Envelope detection, binary |base|  */
} tseq_rx_type_t;

/**
 * Symbol-to-cyclic-shift mapping type (patent Eq. 3).
 */
typedef enum {
    TSEQ_MAP_DECIMAL = 0,  /**< g = decimal(s_m) — default           */
    TSEQ_MAP_GRAY    = 1   /**< g = Gray code mapping                */
} tseq_map_type_t;

/**
 * Transmitter configuration.
 */
typedef struct {
    uint32_t       k;          /**< Symbol size in bits (3, 4, or 5)  */
    uint32_t       N;          /**< Sequence length = 2^k             */
    tseq_map_type_t map_type;  /**< Symbol → cyclic shift mapping     */
    tseq_seq_t     base;       /**< Base ternary sequence             */
    tseq_seq_t     codeset[TSEQ_MAX_N]; /**< All N cyclic shifts     */
} tseq_tx_config_t;

/**
 * Receiver configuration.
 */
typedef struct {
    uint32_t       k;          /**< Symbol size in bits               */
    uint32_t       N;          /**< Sequence length = 2^k             */
    tseq_rx_type_t rx_type;    /**< Coherent or non-coherent          */
    tseq_map_type_t map_type;  /**< Cyclic shift → symbol mapping     */
    tseq_seq_t     base;       /**< Base ternary sequence             */
    tseq_seq_t     ref_set[TSEQ_MAX_N];  /**< Reference sequences:
                                    coherent: cyclic shifts of base
                                    non-coherent: cyclic shifts of |base| */
} tseq_rx_config_t;

/**
 * Correlation result for one cyclic shift.
 */
typedef struct {
    uint32_t  shift;       /**< Cyclic shift g                        */
    int32_t   corr_value;  /**< Correlation value Corr_g              */
} tseq_corr_result_t;

/**
 * Demodulation result for one received sequence.
 */
typedef struct {
    uint32_t  best_shift;   /**< g_est = argmax(Corr_g)              */
    int32_t   max_corr;     /**< Maximum correlation value           */
    uint32_t  symbol;       /**< Detected symbol s_est = f^{-1}(g)  */
    tseq_corr_result_t all_corr[TSEQ_MAX_N]; /**< All N correlations */
} tseq_demod_result_t;

/**
 * Transmit frame — a sequence of modulated ternary sequences.
 */
typedef struct {
    tseq_seq_t  sequences[TSEQ_MAX_FRAME_SYMBOLS];
    uint32_t    num_symbols;
    uint32_t    k;            /**< Bits per symbol                   */
} tseq_frame_t;

/**
 * Modem HAL state — combines TX and RX configuration.
 */
typedef struct {
    tseq_tx_config_t tx;
    tseq_rx_config_t rx;
    int              initialised;
    uint32_t         family_id;  /**< OOK family in use              */
} tseq_modem_t;

/* ===================================================================== */
/* Inline Utilities                                                      */
/* ===================================================================== */

/**
 * Map a symbol to a cyclic shift (patent Eq. 3).
 * Decimal mapping: g = s_m (identity).
 * Gray mapping: g = Gray(s_m).
 */
static inline uint32_t tseq_symbol_to_shift(uint32_t symbol,
                                             tseq_map_type_t map_type)
{
    if (map_type == TSEQ_MAP_GRAY)
        return symbol ^ (symbol >> 1);
    return symbol;  /* decimal mapping */
}

/**
 * Inverse-map a cyclic shift to a symbol (patent Eq. 4).
 */
static inline uint32_t tseq_shift_to_symbol(uint32_t shift,
                                             tseq_map_type_t map_type)
{
    if (map_type == TSEQ_MAP_GRAY) {
        /* Inverse Gray code */
        uint32_t s = shift;
        for (uint32_t mask = s >> 1; mask; mask >>= 1)
            s ^= mask;
        return s;
    }
    return shift;  /* decimal mapping */
}

/* ===================================================================== */
/* Core API — implemented in samsung_tseq_modem.c                        */
/* ===================================================================== */

/**
 * Initialise a modem using a predefined OOK family.
 * Sets up TX and RX configuration with the appropriate base sequence
 * and precomputed codeset / reference set.
 *
 * @param modem     Output modem state.
 * @param family_id TSEQ_FAMILY_3_8, _4_16, or _5_32.
 * @param rx_type   Coherent or non-coherent receiver.
 * @param map_type  Symbol mapping (decimal or Gray).
 * @return 0 on success, -1 on error.
 */
int tseq_modem_init(tseq_modem_t *modem,
                    uint32_t family_id,
                    tseq_rx_type_t rx_type,
                    tseq_map_type_t map_type);

/**
 * Initialise a modem with a custom base ternary sequence.
 * @param modem   Output modem state.
 * @param base    User-provided base ternary sequence.
 * @param k       Symbol size in bits.
 * @param rx_type Coherent or non-coherent.
 * @param map_type Mapping type.
 * @return 0 on success, -1 on error.
 */
int tseq_modem_init_custom(tseq_modem_t *modem,
                           const tseq_seq_t *base,
                           uint32_t k,
                           tseq_rx_type_t rx_type,
                           tseq_map_type_t map_type);

/**
 * Shut down the modem, clearing all state.
 */
void tseq_modem_shutdown(tseq_modem_t *modem);

/**
 * Modulate: encode a k-bit symbol as a ternary sequence.
 * Returns the cyclic shift c_g of the base sequence.
 *
 * @param modem   Initialised modem.
 * @param symbol  k-bit data symbol (0 ≤ symbol < N).
 * @param out     Output ternary sequence c_g.
 * @return 0 on success, -1 if symbol out of range.
 */
int tseq_modulate(const tseq_modem_t *modem,
                  uint32_t symbol,
                  tseq_seq_t *out);

/**
 * Modulate a byte array into a frame of ternary sequences.
 *
 * @param modem    Initialised modem.
 * @param data     Input data bytes.
 * @param data_len Length in bytes.
 * @param frame    Output frame containing modulated sequences.
 * @return Number of symbols generated, or -1 on error.
 */
int tseq_modulate_frame(const tseq_modem_t *modem,
                        const uint8_t *data,
                        size_t data_len,
                        tseq_frame_t *frame);

/**
 * Demodulate: detect a symbol from a received ternary sequence.
 * Performs correlation with all N reference sequences (patent §304-305).
 *
 * @param modem    Initialised modem.
 * @param received Received ternary sequence (possibly noisy).
 * @param result   Output demodulation result.
 * @return 0 on success, -1 on error.
 */
int tseq_demodulate(const tseq_modem_t *modem,
                    const tseq_seq_t *received,
                    tseq_demod_result_t *result);

/**
 * Demodulate a complete frame of received ternary sequences.
 *
 * @param modem       Initialised modem.
 * @param frame       Frame of received sequences.
 * @param symbols_out Output symbol array (capacity ≥ frame->num_symbols).
 * @param max_symbols Capacity of symbols_out.
 * @return Number of symbols detected, or -1 on error.
 */
int tseq_demodulate_frame(const tseq_modem_t *modem,
                          const tseq_frame_t *frame,
                          uint32_t *symbols_out,
                          uint32_t max_symbols);

/**
 * Compute Signal-to-Noise Ratio (SNR) estimate from demodulation result.
 * Uses ratio of max correlation to mean of other correlations.
 *
 * @param result  Demodulation result.
 * @param N       Number of cyclic shifts.
 * @return Estimated SNR in dB (approximate).
 */
double tseq_estimate_snr(const tseq_demod_result_t *result, uint32_t N);

/**
 * Add simulated AWGN noise to a ternary sequence for testing.
 * Applies random bit flips with a given error probability.
 *
 * @param seq     Sequence to corrupt (in-place).
 * @param error_p Probability of flipping each element (0.0 to 1.0).
 * @param seed    PRNG seed for reproducibility.
 */
void tseq_add_noise(tseq_seq_t *seq, double error_p, uint32_t seed);

#ifdef __cplusplus
}
#endif

#endif /* SET5_SAMSUNG_TSEQ_MODEM_H */
