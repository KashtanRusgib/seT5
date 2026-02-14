/**
 * @file srbc.h
 * @brief seT5 Self-Referential Bias Calibration (SRBC) Engine
 *
 * Software-defined feedback control for stabilizing the intermediate
 * "1" state in ternary DLFET-RM logic. Models the "electronic gauge
 * block" architecture described in Samsung's FBFET patents.
 *
 * Key features:
 *   - Dynamic Vth recalibration (DVR) loop
 *   - Thermal drift compensation
 *   - Signal-to-Noise Margin (SNM) monitoring
 *   - Process-Voltage-Temperature (PVT) variation tracking
 *   - Reference cell comparison for self-healing
 *   - State stability window analysis
 *   - Tamper detection via equilibrium disruption
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Self-Referential Bias Calibration
 * @see dlfet_sim.h for DLFET device model
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SRBC_H
#define SET5_SRBC_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Target voltage for state 1 (mV) */
#define SRBC_V_TARGET_MV      400

/** Maximum allowable drift before recalibration (mV) */
#define SRBC_MAX_DRIFT_MV     25

/** Thermal coefficient (µV/°C) */
#define SRBC_THERMAL_COEFF_UV 500

/** Default reference cell count */
#define SRBC_NUM_REF_CELLS    4

/** Maximum calibration history entries */
#define SRBC_MAX_HISTORY      64

/** Stability states */
typedef enum {
    SRBC_STABLE,           /**< State 1 within noise margin */
    SRBC_DRIFTING,         /**< Approaching margin boundary */
    SRBC_RECALIBRATING,    /**< Active recalibration in progress */
    SRBC_TAMPERED,         /**< Equilibrium disrupted (fault/attack) */
    SRBC_FAILED            /**< Unable to stabilize */
} srbc_status_t;

/* ==== Structures ======================================================= */

/**
 * @brief Reference cell state (the "gauge block").
 */
typedef struct {
    int   vth_nominal_mv;      /**< Nominal threshold voltage */
    int   vth_actual_mv;       /**< Current measured Vth */
    int   leakage_na;          /**< Reference leakage current (nA) */
    int   temperature_mc;      /**< Temperature (milli-Celsius) */
    int   drift_mv;            /**< Accumulated drift from nominal */
} srbc_ref_cell_t;

/**
 * @brief Calibration event record.
 */
typedef struct {
    int   timestamp;           /**< Tick count at calibration */
    int   drift_before_mv;     /**< Drift that triggered recal */
    int   correction_mv;       /**< Applied correction */
    int   temperature_mc;      /**< Temperature at event */
    srbc_status_t  status;     /**< Resulting status */
} srbc_cal_event_t;

/**
 * @brief SRBC engine state.
 */
typedef struct {
    srbc_ref_cell_t  ref_cells[SRBC_NUM_REF_CELLS]; /**< Reference cells */
    int              num_ref_cells;                   /**< Active ref cells */
    srbc_status_t    status;                          /**< Current status */

    /* Feedback loop state */
    int   v_target_mv;         /**< Target intermediate voltage */
    int   v_current_mv;        /**< Current measured voltage */
    int   snm_mv;              /**< Current Signal-to-Noise Margin */
    int   correction_mv;       /**< Last applied correction */

    /* PVT tracking */
    int   temperature_mc;      /**< Current temp (milli-Celsius) */
    int   supply_mv;           /**< Current supply voltage */
    int   process_corner;      /**< -1=slow, 0=typical, +1=fast */

    /* Statistics */
    int   total_calibrations;  /**< Total recalibration events */
    int   tamper_events;       /**< Detected tamper attempts */
    int   stability_pct;       /**< Uptime in stable state (0-100) */
    int   ticks;               /**< Total tick count */
    int   stable_ticks;        /**< Ticks in stable state */

    /* History */
    srbc_cal_event_t history[SRBC_MAX_HISTORY];
    int              history_count;
} srbc_state_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize SRBC engine with nominal parameters.
 * @param state  SRBC state to initialize.
 */
void srbc_init(srbc_state_t *state);

/**
 * @brief Execute one calibration tick.
 *
 * Reads reference cells, computes drift, applies correction if
 * drift exceeds threshold. Models the negative feedback loop.
 *
 * @param state  SRBC state.
 * @return       Current status after tick.
 */
srbc_status_t srbc_tick(srbc_state_t *state);

/**
 * @brief Apply thermal disturbance.
 *
 * Simulates temperature change affecting Vth via thermal coefficient.
 *
 * @param state      SRBC state.
 * @param delta_mc   Temperature change (milli-Celsius).
 */
void srbc_apply_thermal(srbc_state_t *state, int delta_mc);

/**
 * @brief Apply supply voltage variation.
 *
 * @param state      SRBC state.
 * @param new_vdd_mv New supply voltage (mV).
 */
void srbc_apply_voltage(srbc_state_t *state, int new_vdd_mv);

/**
 * @brief Simulate tamper attempt (fault injection).
 *
 * Models laser/EM probe disrupting the reference equilibrium.
 *
 * @param state       SRBC state.
 * @param inject_mv   Injected voltage disturbance (mV).
 * @return            1 if tamper detected, 0 if absorbed.
 */
int srbc_inject_fault(srbc_state_t *state, int inject_mv);

/**
 * @brief Query current Signal-to-Noise Margin.
 * @param state  SRBC state.
 * @return       SNM in millivolts.
 */
int srbc_get_snm(const srbc_state_t *state);

/**
 * @brief Query stability percentage (uptime in STABLE state).
 * @param state  SRBC state.
 * @return       Percentage (0-100).
 */
int srbc_get_stability(const srbc_state_t *state);

/**
 * @brief Reset all reference cells to nominal.
 * @param state  SRBC state.
 */
void srbc_reset_refs(srbc_state_t *state);

/**
 * @brief Map SRBC-stabilized state to balanced ternary trit.
 *
 * Returns TRIT_FALSE if voltage < V_target - margin,
 *         TRIT_TRUE if voltage > V_target + margin,
 *         TRIT_UNKNOWN if within the stable "1" window.
 *
 * @param voltage_mv  Measured voltage.
 * @return            Corresponding trit value.
 */
trit srbc_voltage_to_trit(int voltage_mv);

#ifdef __cplusplus
}
#endif

#endif /* SET5_SRBC_H */
