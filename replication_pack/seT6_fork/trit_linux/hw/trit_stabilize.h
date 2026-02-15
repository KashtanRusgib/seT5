/**
 * @file trit_stabilize.h
 * @brief seT6 Trit Stability Engine — PVT variation, thermal noise,
 *        cosmic-ray trit-flip simulation, and self-calibrating feedback.
 *
 * Models the physics-accurate emulation of trit stability under
 * Process, Voltage, and Temperature (PVT) corner variations.
 * Integrates with SRBC (gauge-block) for self-healing loops and
 * DLFET for gate-level simulation of the "1" state.
 *
 * Key features:
 *   - PVT corner sweeps (slow/typical/fast × voltage × temp)
 *   - Thermal noise injection with configurable amplitude
 *   - Cosmic-ray single-event upset (SEU) trit-flip simulation
 *   - Meta-stable state detection and recovery
 *   - Stability window analysis (noise margin in mV)
 *   - Integration with SRBC for self-calibrating loops
 *   - Statistical reporting for Sigma 9 validation
 *
 * @see srbc.h for gauge-block calibration
 * @see dlfet_sim.h for DLFET device model
 * @see prop_delay.h for propagation delay under PVT
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_STABILIZE_H
#define SET6_TRIT_STABILIZE_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Maximum PVT sweep configurations */
#define TSTAB_MAX_PVT_CONFIGS    27   /* 3 corners × 3 voltages × 3 temps */

/** Noise injection types */
#define TSTAB_NOISE_THERMAL      0x01
#define TSTAB_NOISE_FLICKER      0x02
#define TSTAB_NOISE_SHOT         0x04
#define TSTAB_NOISE_ALL          0x07

/** SEU (cosmic ray) parameters */
#define TSTAB_SEU_PROB_PPM       10    /* 10 parts-per-million default */
#define TSTAB_MAX_FLIPS_LOG      256   /* Max flip events to log */

/** Meta-stable detection thresholds */
#define TSTAB_METASTABLE_MV      15    /* Within ±15mV of decision boundary */
#define TSTAB_RECOVERY_CYCLES    5     /* Cycles to resolve meta-stability */

/** PVT corners */
#define TSTAB_CORNER_SLOW       (-1)
#define TSTAB_CORNER_TYPICAL     (0)
#define TSTAB_CORNER_FAST        (1)

/* ==== Structures ======================================================= */

/**
 * @brief PVT configuration for a single sweep point.
 */
typedef struct {
    int   process_corner;      /**< SLOW/TYPICAL/FAST (-1/0/+1) */
    int   voltage_mv;          /**< Supply voltage (mV) */
    int   temperature_mc;      /**< Temperature (milli-Celsius) */
} tstab_pvt_config_t;

/**
 * @brief Result of running a trit through a PVT configuration.
 */
typedef struct {
    trit  input;               /**< Original trit value */
    trit  output;              /**< Output after PVT effects */
    int   flipped;             /**< 1 if trit changed value */
    int   metastable;          /**< 1 if entered meta-stable state */
    int   recovery_cycles;     /**< Cycles needed to resolve (0 if clean) */
    int   noise_mv;            /**< Applied noise amplitude (mV) */
    int   snm_mv;              /**< Signal-to-noise margin remaining */
} tstab_pvt_result_t;

/**
 * @brief Cosmic-ray trit-flip event record.
 */
typedef struct {
    int   tick;                /**< When the flip occurred */
    int   position;            /**< Which trit position was hit */
    trit  before;              /**< Value before flip */
    trit  after;               /**< Value after flip */
    int   recovered;           /**< 1 if self-healed via SRBC */
} tstab_flip_event_t;

/**
 * @brief Main stability engine state.
 */
typedef struct {
    int   initialized;

    /* Noise model */
    int   noise_types;         /**< Bitmask of enabled noise types */
    int   noise_amplitude_mv;  /**< Peak-to-peak noise (mV) */
    uint32_t rng_seed;         /**< PRNG state for deterministic replay */

    /* SEU model */
    int   seu_prob_ppm;        /**< SEU probability (parts per million) */
    tstab_flip_event_t flips[TSTAB_MAX_FLIPS_LOG];
    int   flip_count;          /**< Recorded flip events */
    int   flips_recovered;     /**< Self-healed flips */
    int   flips_permanent;     /**< Unrecoverable flips */

    /* PVT sweep */
    tstab_pvt_config_t  pvt_configs[TSTAB_MAX_PVT_CONFIGS];
    tstab_pvt_result_t  pvt_results[TSTAB_MAX_PVT_CONFIGS];
    int   pvt_config_count;
    int   pvt_sweep_done;

    /* Meta-stability tracking */
    int   metastable_events;   /**< Total meta-stable detections */
    int   metastable_resolved; /**< Successfully resolved */
    int   metastable_failed;   /**< Failed to resolve → trit flip */

    /* Statistics */
    int   total_trits_tested;
    int   total_stable;        /**< Trits that held through noise */
    int   total_flipped;       /**< Trits that were corrupted */
    int   worst_snm_mv;        /**< Lowest observed SNM */
    int   stability_ppm;       /**< Parts per million stable */
} tstab_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize the stability engine.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int tstab_init(tstab_state_t *st);

/**
 * @brief Configure noise injection model.
 * @param st           State.
 * @param noise_types  Bitmask of TSTAB_NOISE_* types.
 * @param amplitude_mv Peak noise amplitude (mV).
 * @param seed         PRNG seed for reproducibility.
 * @return 0 on success, -1 on error.
 */
int tstab_configure_noise(tstab_state_t *st, int noise_types,
                          int amplitude_mv, uint32_t seed);

/**
 * @brief Configure SEU (cosmic ray) model.
 * @param st       State.
 * @param prob_ppm Probability in parts-per-million per tick.
 * @return 0 on success.
 */
int tstab_configure_seu(tstab_state_t *st, int prob_ppm);

/**
 * @brief Generate all PVT corner configurations (3×3×3 = 27 points).
 *
 * Sweeps: corners {slow, typical, fast}, voltages {700, 800, 900 mV},
 * temperatures {-40000, 25000, 125000 mC}.
 *
 * @param st  State to populate.
 * @return Number of configs generated (27).
 */
int tstab_generate_pvt_sweep(tstab_state_t *st);

/**
 * @brief Run a single trit through one PVT corner, applying noise.
 * @param st      State.
 * @param input   Trit to test.
 * @param config  PVT configuration.
 * @param result  Output result.
 * @return 0 on success.
 */
int tstab_test_trit_pvt(tstab_state_t *st, trit input,
                        const tstab_pvt_config_t *config,
                        tstab_pvt_result_t *result);

/**
 * @brief Run full PVT sweep on all three trit values.
 *
 * Tests TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE across all 27 PVT configs
 * (81 total test points). Updates statistics.
 *
 * @param st  State with PVT configs generated.
 * @return Number of trit flips detected (0 = perfect stability).
 */
int tstab_run_full_sweep(tstab_state_t *st);

/**
 * @brief Simulate a cosmic-ray single-event upset on a trit array.
 * @param st     State.
 * @param trits  Array of trits.
 * @param count  Number of trits.
 * @param tick   Current simulation tick.
 * @return Number of flips injected.
 */
int tstab_inject_seu(tstab_state_t *st, trit *trits, int count, int tick);

/**
 * @brief Attempt to recover flipped trits using SRBC self-calibration.
 * @param st     State.
 * @param trits  Array (may be corrected in-place).
 * @param orig   Original (known-good) reference array.
 * @param count  Number of trits.
 * @return Number of trits successfully recovered.
 */
int tstab_recover_seu(tstab_state_t *st, trit *trits,
                      const trit *orig, int count);

/**
 * @brief Detect meta-stable trits in an array.
 *
 * A trit is meta-stable if the underlying voltage is within
 * ±TSTAB_METASTABLE_MV of a decision boundary.
 *
 * @param st      State.
 * @param voltages_mv  Voltage representation of trits.
 * @param count   Number of entries.
 * @return Number of meta-stable trits detected.
 */
int tstab_detect_metastable(tstab_state_t *st, const int *voltages_mv,
                            int count);

/**
 * @brief Compute stability in parts-per-million.
 * @param st  State after tests.
 * @return PPM of trits that remained stable (1000000 = perfect).
 */
int tstab_get_stability_ppm(const tstab_state_t *st);

/**
 * @brief Query worst-case signal-to-noise margin observed.
 * @param st  State.
 * @return Worst SNM in millivolts.
 */
int tstab_get_worst_snm(const tstab_state_t *st);

/**
 * @brief Apply CNTFET drift as additional PVT noise source.
 *
 * Adds drift_mv to the noise model, increasing the effective noise
 * amplitude for subsequent PVT tests.  Allows combining CNTFET
 * device-level drift with the stabilize engine's system-level analysis.
 *
 * @param st        Stabilize state.
 * @param drift_mv  CNTFET drift to incorporate (mV).
 * @return New total noise amplitude (mV), or -1 on error.
 */
int tstab_apply_cntfet_drift(tstab_state_t *st, int drift_mv);

/**
 * @brief Apply Tekum tapered-precision truncation to PVT sweep results.
 *
 * Truncates PVT noise margin values using Tekum format's rounding=truncation
 * property. Demonstrates that balanced ternary truncation preserves signal
 * integrity better than binary truncation.
 *
 * @param st         Stabilize state (must have run PVT sweep).
 * @param from_trits Original tekum width (must be even >= 8).
 * @param to_trits   Target tekum width (must be even >= 8, < from_trits).
 * @return Maximum truncation error ×1000 across all PVT results
 *         (should be < 500 = 0.5 ulp), or -1 on error.
 */
int tstab_tekum_taper(tstab_state_t *st, int from_trits, int to_trits);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_STABILIZE_H */
