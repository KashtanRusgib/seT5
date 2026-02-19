/**
 * @file trit_pretrain_scale.h
 * @brief seT6 Ternary Pretraining Scaling Laws (TriLMs)
 *
 * Implements scaling law estimation and bit-equivalent performance
 * prediction for ternary pretrained models, based on the TriLMs paper
 * (ICLR 2025). Key insight: ternary models pretrained from scratch
 * outperform post-quantized float models at >1B parameters.
 *
 * Key features:
 *   - Scaling law prediction: loss(N, D, b) for N params, D tokens, b bits
 *   - Bit-equivalent parameter count: ternary 1.58 bits/weight
 *   - TriLM vs QuantLM crossover estimation
 *   - Spectra suite emulation (99M–3.9B configs)
 *   - Perplexity estimation from loss
 *   - Memory bandwidth savings (1.58 vs 16 bits → 10.1× reduction)
 *   - FLOP estimation for ternary MAC-free ops
 *
 * Scaling law (Chinchilla-style, ternary-adjusted):
 *   L(N,D) = A / N^α + B / D^β + E
 *   For ternary: effective_params = N × (1.58 / 16)
 *   Crossover: TriLM beats QuantLM when N > N_cross
 *
 * Reference: "Scaling Laws for TriLMs at Scale", ICLR 2025
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_PRETRAIN_SCALE_H
#define SET6_TRIT_PRETRAIN_SCALE_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define TPS_FP_SCALE          1000    /**< Fixed-point scale ×1000         */
#define TPS_BITS_PER_TERNARY  1580    /**< 1.58 bits ×1000                */
#define TPS_BITS_PER_FLOAT    16000   /**< 16 bits ×1000 (FP16 reference) */
#define TPS_BITS_PER_BINARY   1000    /**< 1 bit ×1000 (binary reference) */
#define TPS_MAX_CONFIGS       16      /**< Max Spectra configurations      */

/* Chinchilla scaling constants (×1000) — fitted to TriLM data */
#define TPS_CHINCHILLA_A      406000  /**< A = 406.0 (loss prefactor)     */
#define TPS_CHINCHILLA_ALPHA  340     /**< α = 0.340 (param exponent)     */
#define TPS_CHINCHILLA_B      410000  /**< B = 410.0 (data prefactor)     */
#define TPS_CHINCHILLA_BETA   280     /**< β = 0.280 (data exponent)      */
#define TPS_CHINCHILLA_E      1690    /**< E = 1.690 (irreducible loss)   */

/** Spectra suite model sizes (millions of parameters) */
#define TPS_SPECTRA_99M       99
#define TPS_SPECTRA_197M      197
#define TPS_SPECTRA_394M      394
#define TPS_SPECTRA_830M      830
#define TPS_SPECTRA_1B7       1700
#define TPS_SPECTRA_3B9       3900

/* ==== Structures ======================================================== */

/**
 * @brief Model configuration for scaling law evaluation.
 */
typedef struct {
    int  params_m;          /**< Parameters in millions               */
    int  tokens_b;          /**< Training tokens in billions          */
    int  bits_per_weight;   /**< Bits per weight ×1000 (1580 for ternary) */
    int  estimated_loss;    /**< Predicted loss ×1000                 */
    int  estimated_ppl;     /**< Predicted perplexity ×100            */
    int  bit_equiv_params;  /**< Bit-equivalent params in millions   */
    int  memory_mb;         /**< Estimated memory in MB               */
    int64_t flops;          /**< Estimated training FLOPs             */
} tps_config_t;

/**
 * @brief Scaling law engine state.
 */
typedef struct {
    int           initialized;
    tps_config_t  configs[TPS_MAX_CONFIGS];
    int           config_count;
    int           crossover_params_m;   /**< N where TriLM > QuantLM      */
} tps_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize scaling law engine.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int tps_init(tps_state_t *st);

/**
 * @brief Compute bit-equivalent parameter count.
 *
 * effective_params = N × (bits_per_weight / 16)
 * For ternary (1.58 bits): effective ≈ N × 0.099 of FP16
 *
 * @param params_m         Parameters in millions.
 * @param bits_per_weight  Bits per weight ×1000.
 * @return Bit-equivalent parameters in millions.
 */
int tps_bit_equivalent(int params_m, int bits_per_weight);

/**
 * @brief Estimate loss using Chinchilla scaling law (ternary-adjusted).
 *
 * L(N,D) = A / N^α + B / D^β + E
 * Uses integer approximation of power-law.
 *
 * @param params_m  Parameters in millions.
 * @param tokens_b  Training tokens in billions.
 * @return Estimated loss ×1000.
 */
int tps_estimate_loss(int params_m, int tokens_b);

/**
 * @brief Convert loss to perplexity: PPL = exp(loss).
 * @param loss  Loss ×1000.
 * @return Perplexity ×100.
 */
int tps_loss_to_ppl(int loss);

/**
 * @brief Estimate memory requirement for ternary model.
 *
 * memory_MB = params × bits_per_weight / 8 / 1e6
 * For ternary: ~0.198 MB per million params.
 *
 * @param params_m         Parameters in millions.
 * @param bits_per_weight  Bits per weight ×1000.
 * @return Memory in MB.
 */
int tps_estimate_memory(int params_m, int bits_per_weight);

/**
 * @brief Compute memory bandwidth saving ratio vs FP16 × 1000.
 *
 * ratio = FP16_bits / ternary_bits = 16 / 1.58 ≈ 10.1×
 *
 * @param bits_per_weight  Bits per weight ×1000.
 * @return Savings ratio ×1000.
 */
int tps_bandwidth_saving(int bits_per_weight);

/**
 * @brief Add a model configuration and compute all metrics.
 * @param st              State.
 * @param params_m        Parameters in millions.
 * @param tokens_b        Training tokens in billions.
 * @param bits_per_weight Bits per weight ×1000.
 * @return Config index (>=0), or -1 on error.
 */
int tps_add_config(tps_state_t *st, int params_m, int tokens_b,
                   int bits_per_weight);

/**
 * @brief Estimate crossover point where TriLM beats QuantLM.
 *
 * Iterates scaling law to find N where ternary-pretrained loss
 * is lower than post-quantized loss.
 *
 * @param st        State.
 * @param tokens_b  Training tokens in billions.
 * @return Crossover parameter count in millions (0 if no crossover).
 */
int tps_find_crossover(tps_state_t *st, int tokens_b);

/**
 * @brief Estimate training FLOPs (6 × N × D approximation).
 *
 * Standard: FLOPs ≈ 6 × N × D.
 * Ternary MAC-free: FLOPs_effective ≈ 6 × N × D × 0.33
 * (only addition needed, no multiplication).
 *
 * @param params_m  Parameters in millions.
 * @param tokens_b  Training tokens in billions.
 * @return Estimated FLOPs (may overflow for large models).
 */
int64_t tps_estimate_flops(int params_m, int tokens_b);

/**
 * @brief Estimate loss using bit-size scaling law (TriLMs arXiv).
 *
 * loss = A / bits^α + ε
 * where α = 0.26 (fitted from TriLMs data) and bits = total_bits
 * = params × bits_per_weight.
 *
 * This is the simplified per-bit scaling law from Section 4 of TriLMs.
 *
 * @param total_bits_m  Total model bits in millions (params × bpw / 1000).
 * @return Estimated loss ×1000.
 */
int tps_bitsize_scaling(int total_bits_m);

/**
 * @brief Find the bit-count where ternary pretrained matches float.
 *
 * Sweeps total_bits from 100M to 100000M to find where
 * ternary loss ≤ float loss (crossover point for pretrained ternary).
 *
 * @param float_loss_x1000  Target float-model loss ×1000.
 * @return Total bits in millions at crossover, or 0 if not found.
 */
int tps_crossover_bits(int float_loss_x1000);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_PRETRAIN_SCALE_H */
