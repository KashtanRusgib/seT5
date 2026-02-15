/**
 * @file qemu_trit.h
 * @brief seT6 QEMU Extension — Ternary Noise Simulation
 *
 * Simulates the analog uncertainty inherent in real ternary hardware.
 * In physical ternary circuits (CMOS-ternary, memristive 1T1M), the
 * boundary between voltage levels is noisy, causing occasional
 * Unknown-to-True or Unknown-to-False flips.
 *
 * This module models that noise to stress-test the kernel's Unknown
 * propagation guarantees. A correct seT6 kernel must function
 * identically regardless of noise — all Unknown values are treated
 * conservatively.
 *
 * Noise models:
 *   1. UNIFORM:   Each trit has p probability of flipping to Unknown
 *   2. GAUSSIAN:  Voltage-threshold model with σ noise band
 *   3. MEMRISTIVE: Resistance drift model (1T1M TMR aging)
 *   4. COSMIC:    Single-event upset (SEU) — random bit flip in trit2
 *
 * Integration:
 *   - Attach to kernel_state_t as a noise injection layer
 *   - Intercepts mem_read/mem_write and trit register accesses
 *   - Counts injected faults and tracks recovery
 *
 * @see ARCHITECTURE.md §10 — QEMU Noise Simulation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_QEMU_TRIT_H
#define SET6_QEMU_TRIT_H

#include "set6/trit.h"
#include "set6/trit_emu.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Noise Models ----------------------------------------------------- */

typedef enum {
    NOISE_NONE       = 0, /**< No noise (deterministic) */
    NOISE_UNIFORM    = 1, /**< Uniform random flip to Unknown */
    NOISE_GAUSSIAN   = 2, /**< Voltage-threshold Gaussian noise */
    NOISE_MEMRISTIVE = 3, /**< Resistance drift aging model */
    NOISE_COSMIC     = 4  /**< Single-event upset (bit flip) */
} noise_model_t;

/* ---- QEMU Ternary Noise State ---------------------------------------- */

/**
 * @brief State for the QEMU ternary noise simulator.
 */
typedef struct {
    noise_model_t model;        /**< Active noise model */
    uint32_t      seed;         /**< PRNG seed (xorshift32) */
    int           flip_prob_ppm;/**< Flip probability in parts-per-million */
    int           total_reads;  /**< Total trit reads intercepted */
    int           total_writes; /**< Total trit writes intercepted */
    int           faults_injected; /**< Faults injected (flips to Unknown) */
    int           faults_cosmic;   /**< Cosmic ray bit flips */
    int           drift_cycles; /**< Memristive drift cycle counter */
    int           enabled;      /**< 1 = noise active, 0 = passthrough */
} qemu_noise_t;

/* ---- PRNG (xorshift32) ----------------------------------------------- */

/**
 * @brief Fast 32-bit PRNG for noise injection.
 *
 * Marsaglia's xorshift32 — period 2^32-1, sufficient for simulation.
 * NOT cryptographically secure — only for noise modeling.
 *
 * @param state  PRNG state (modified in-place).
 * @return       Next pseudo-random value.
 */
static inline uint32_t qemu_xorshift32(uint32_t *state) {
    uint32_t x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    return x;
}

/* ---- API -------------------------------------------------------------- */

/**
 * @brief Initialise the noise simulator.
 *
 * @param noise     Noise state to initialise.
 * @param model     Noise model to use.
 * @param seed      PRNG seed (use 0 for deterministic default).
 * @param prob_ppm  Flip probability in parts per million (e.g., 1000 = 0.1%).
 */
static inline void qemu_noise_init(qemu_noise_t *noise, noise_model_t model,
                                   uint32_t seed, int prob_ppm) {
    if (!noise) return;
    noise->model           = model;
    noise->seed            = seed ? seed : 0xDEADBEEF;
    noise->flip_prob_ppm   = prob_ppm;
    noise->total_reads     = 0;
    noise->total_writes    = 0;
    noise->faults_injected = 0;
    noise->faults_cosmic   = 0;
    noise->drift_cycles    = 0;
    noise->enabled         = (model != NOISE_NONE) ? 1 : 0;
}

/**
 * @brief Apply noise to a single trit read.
 *
 * Models the physical uncertainty of reading a ternary voltage level.
 * Depending on the noise model:
 *   - UNIFORM: random flip to Unknown with probability prob_ppm/1M
 *   - GAUSSIAN: flip if |value| < threshold (modeled as prob_ppm)
 *   - MEMRISTIVE: increasing drift probability over time
 *   - COSMIC: random bit flip in the 2-bit encoding
 *
 * @param noise  Noise state.
 * @param value  Clean trit value.
 * @return       Possibly corrupted trit value.
 */
static inline trit qemu_noise_read(qemu_noise_t *noise, trit value) {
    if (!noise || !noise->enabled) return value;

    noise->total_reads++;
    uint32_t r = qemu_xorshift32(&noise->seed);

    switch (noise->model) {
    case NOISE_UNIFORM:
        /* Flip to Unknown with probability flip_prob_ppm / 1M */
        if ((int)(r % 1000000) < noise->flip_prob_ppm) {
            noise->faults_injected++;
            return TRIT_UNKNOWN;
        }
        break;

    case NOISE_GAUSSIAN:
        /* Unknown trits are most vulnerable — flip to either side */
        if (value == TRIT_UNKNOWN) {
            if ((int)(r % 1000000) < noise->flip_prob_ppm * 3) {
                noise->faults_injected++;
                return (r & 1) ? TRIT_TRUE : TRIT_FALSE;
            }
        }
        /* Non-unknown trits: smaller flip probability */
        if ((int)(r % 1000000) < noise->flip_prob_ppm) {
            noise->faults_injected++;
            return TRIT_UNKNOWN;
        }
        break;

    case NOISE_MEMRISTIVE:
        /* Drift increases with cycle count */
        noise->drift_cycles++;
        {
            int drift_factor = 1 + (noise->drift_cycles / 10000);
            int effective_prob = noise->flip_prob_ppm * drift_factor;
            if (effective_prob > 500000) effective_prob = 500000; /* cap at 50% */
            if ((int)(r % 1000000) < effective_prob) {
                noise->faults_injected++;
                return TRIT_UNKNOWN;
            }
        }
        break;

    case NOISE_COSMIC:
        /* Rare single-event upset — flip one bit in the 2-bit encoding */
        if ((int)(r % 1000000) < noise->flip_prob_ppm / 10) {
            noise->faults_cosmic++;
            noise->faults_injected++;
            /* XOR bit 0 or bit 1 */
            int encoded = (int)value;
            encoded ^= (1 << (r & 1));
            /* Clamp back to valid range */
            if (encoded < -1 || encoded > 1) return TRIT_UNKNOWN;
            return (trit)encoded;
        }
        break;

    default:
        break;
    }

    return value;
}

/**
 * @brief Apply noise to a 32-trit register read (bulk).
 *
 * Applies the noise model to each trit position independently.
 *
 * @param noise  Noise state.
 * @param reg    32-trit register (modified in-place if noise fires).
 * @return       Number of faults injected in this call.
 */
static inline int qemu_noise_reg32(qemu_noise_t *noise, trit2_reg32 *reg) {
    if (!noise || !noise->enabled || !reg) return 0;

    int injected = 0;
    for (int i = 0; i < 32; i++) {
        trit2 original = trit2_reg32_get(reg, i);
        int decoded = trit2_decode(original);
        trit noisy_scalar = qemu_noise_read(noise, trit_from_int(decoded));
        trit2 noisy_packed = trit_to_trit2(noisy_scalar);
        if (noisy_packed != original) {
            trit2_reg32_set(reg, i, noisy_packed);
            injected++;
        }
    }
    return injected;
}

/**
 * @brief Get noise simulation statistics.
 *
 * @param noise         Noise state.
 * @param[out] reads    Total reads intercepted.
 * @param[out] writes   Total writes intercepted.
 * @param[out] faults   Total faults injected.
 * @param[out] cosmic   Cosmic ray events.
 * @param[out] drift    Drift cycles for memristive model.
 */
static inline void qemu_noise_stats(const qemu_noise_t *noise,
                                    int *reads, int *writes, int *faults,
                                    int *cosmic, int *drift) {
    if (!noise) return;
    if (reads)  *reads  = noise->total_reads;
    if (writes) *writes = noise->total_writes;
    if (faults) *faults = noise->faults_injected;
    if (cosmic) *cosmic = noise->faults_cosmic;
    if (drift)  *drift  = noise->drift_cycles;
}

/**
 * @brief Reset noise statistics without changing model.
 * @param noise  Noise state.
 */
static inline void qemu_noise_reset_stats(qemu_noise_t *noise) {
    if (!noise) return;
    noise->total_reads     = 0;
    noise->total_writes    = 0;
    noise->faults_injected = 0;
    noise->faults_cosmic   = 0;
    noise->drift_cycles    = 0;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_QEMU_TRIT_H */
