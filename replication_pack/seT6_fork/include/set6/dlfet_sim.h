/**
 * @file dlfet_sim.h
 * @brief seT6 Doping-Less FET with Resistive Memory (DLFET-RM) Simulator
 *
 * Behavioral simulation of Samsung/UNIST DLFET-RM ternary logic gates
 * for pre-silicon validation. Models:
 *
 *   - Threshold voltage (Vth) modulation via charge plasma
 *   - Three stable states: Depleted (0), Partial Depletion (1), Accumulated (2)
 *   - Resistive Memory (RM) element HRS/LRS transitions
 *   - Self-referential bias calibration feedback loop
 *   - Standard Ternary Inverter (STI/TNOT)
 *   - Ternary NAND (TNAND) with DLFET-RM biasing
 *   - Ternary NOR (TNOR)
 *   - Ternary Half Adder / Full Adder (THA/TFA)
 *   - Power-Delay Product (PDP) estimation
 *   - Noise margin analysis
 *
 * Uses unbalanced ternary (0, 1, 2) internally for hardware fidelity,
 * with conversion to/from balanced ternary {-1, 0, +1} for seT6 integration.
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Virtual Doping-Less FET
 * @see hw/ternary_full_adder.v for synthesizable RTL
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_DLFET_SIM_H
#define SET6_DLFET_SIM_H

#include "set6/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ======================================================== */

/** Voltage levels in millivolts */
#define DLFET_VDD_MV        800    /**< Supply voltage (mV) */
#define DLFET_V_MID_MV      400    /**< Intermediate "1" state voltage */
#define DLFET_VTH_NOM_MV    350    /**< Nominal threshold voltage */
#define DLFET_NOISE_MARGIN_MV 50   /**< Minimum noise margin */

/** Transistor counts for area estimation */
#define DLFET_TNOT_TRANSISTORS   4
#define DLFET_TNAND_TRANSISTORS  14
#define DLFET_TNOR_TRANSISTORS   14
#define DLFET_THA_TRANSISTORS    42
#define DLFET_TFA_TRANSISTORS    93

/** Energy per operation (atto-Joules) at 0.5 GHz */
#define DLFET_PDP_TNOT_AJ       3
#define DLFET_PDP_TNAND_AJ      8
#define DLFET_PDP_TFA_AJ        11

/** RM element states */
typedef enum {
    RM_HRS,    /**< High Resistance State — logic 0 path */
    RM_LRS     /**< Low Resistance State — logic 1/2 path */
} dlfet_rm_state_t;

/** DLFET channel states */
typedef enum {
    DLFET_DEPLETED,        /**< State 0: fully off */
    DLFET_PARTIAL,         /**< State 1: partial depletion (RM stabilized) */
    DLFET_ACCUMULATED      /**< State 2: fully on */
} dlfet_channel_state_t;

/* ==== DLFET Device Model =============================================== */

/**
 * @brief Single DLFET transistor model.
 */
typedef struct {
    int           vth_mv;          /**< Threshold voltage (mV) */
    int           vgs_mv;          /**< Gate-source voltage (mV) */
    int           vds_mv;          /**< Drain-source voltage (mV) */
    dlfet_rm_state_t    rm_state;  /**< Attached RM element state */
    dlfet_channel_state_t channel; /**< Current channel state */
    int           ids_na;          /**< Drain current (nA) */
    int           vout_mv;         /**< Output voltage (mV) */
} dlfet_device_t;

/**
 * @brief Gate-level simulation state.
 */
typedef struct {
    int   total_gates;             /**< Gates instantiated */
    int   total_transitions;       /**< State transitions counted */
    int   energy_aj;               /**< Accumulated energy (aJ) */
    int   prop_delay_ps;           /**< Last gate propagation delay (ps) */
    int   vth_drift_mv;            /**< Accumulated Vth drift (mV) */
    int   calibration_count;       /**< SRBC recalibration events */
} dlfet_sim_state_t;

/* ==== API ============================================================== */

/** Initialize simulation state. */
void dlfet_sim_init(dlfet_sim_state_t *state);

/** Initialize a single DLFET device with nominal parameters. */
void dlfet_device_init(dlfet_device_t *dev);

/* ---- Unbalanced ternary gates (0, 1, 2) ------ */

/** Ternary inverter (TNOT): 0→2, 1→1, 2→0 */
uint8_t dlfet_tnot(dlfet_sim_state_t *state, uint8_t a);

/** Ternary NAND (TNAND) per Samsung DLFET-RM truth table */
uint8_t dlfet_tnand(dlfet_sim_state_t *state, uint8_t a, uint8_t b);

/** Ternary NOR (TNOR) */
uint8_t dlfet_tnor(dlfet_sim_state_t *state, uint8_t a, uint8_t b);

/** Ternary AND (TAND) = TNOT(TNAND(a,b)) */
uint8_t dlfet_tand(dlfet_sim_state_t *state, uint8_t a, uint8_t b);

/** Ternary OR (TOR) = TNOT(TNOR(a,b)) */
uint8_t dlfet_tor(dlfet_sim_state_t *state, uint8_t a, uint8_t b);

/** Ternary MIN = min(a, b) */
uint8_t dlfet_tmin(dlfet_sim_state_t *state, uint8_t a, uint8_t b);

/** Ternary MAX = max(a, b) */
uint8_t dlfet_tmax(dlfet_sim_state_t *state, uint8_t a, uint8_t b);

/* ---- Arithmetic ------ */

/**
 * @brief Ternary Half Adder: sum = (a + b) mod 3, carry = (a + b) / 3
 */
void dlfet_ternary_half_adder(dlfet_sim_state_t *state,
                               uint8_t a, uint8_t b,
                               uint8_t *sum, uint8_t *carry);

/**
 * @brief Ternary Full Adder: sum = (a + b + cin) mod 3, cout = (a + b + cin) / 3
 */
void dlfet_ternary_full_adder(dlfet_sim_state_t *state,
                               uint8_t a, uint8_t b, uint8_t cin,
                               uint8_t *sum, uint8_t *cout);

/**
 * @brief Multi-trit ternary addition using ripple-carry TFA chain.
 * @param a      First operand (array of trits in unbalanced 0/1/2).
 * @param b      Second operand.
 * @param result Output sum.
 * @param width  Number of trits.
 * @return       Carry out.
 */
uint8_t dlfet_ternary_add(dlfet_sim_state_t *state,
                           const uint8_t *a, const uint8_t *b,
                           uint8_t *result, int width);

/* ---- Balanced ↔ Unbalanced conversion ------ */

/** Balanced {-1,0,+1} → Unbalanced {0,1,2} */
static inline uint8_t dlfet_balanced_to_unbalanced(trit t) {
    return (uint8_t)(t + 1);
}

/** Unbalanced {0,1,2} → Balanced {-1,0,+1} */
static inline trit dlfet_unbalanced_to_balanced(uint8_t u) {
    return (trit)(u - 1);
}

/* ---- Performance metrics ------ */

/**
 * @brief Estimate Power-Delay Product for a gate configuration.
 * @param gate_type  0=TNOT, 1=TNAND, 2=TNOR, 3=THA, 4=TFA
 * @return           PDP in atto-Joules.
 */
int dlfet_pdp_estimate(int gate_type);

/**
 * @brief Compute noise margin for state 1 stabilization.
 * @param vth_mv  Actual threshold voltage (mV).
 * @return        Noise margin (mV), negative if unstable.
 */
int dlfet_noise_margin(int vth_mv);

/**
 * @brief Get simulation statistics summary.
 */
void dlfet_sim_stats(const dlfet_sim_state_t *state,
                     int *gates, int *transitions, int *energy_aj);

#ifdef __cplusplus
}
#endif

#endif /* SET6_DLFET_SIM_H */
