/**
 * @file prop_delay.h
 * @brief seT6 Propagation Delay Variance Model
 *
 * Models the asymmetric propagation delays in DLFET-RM ternary
 * logic gates. Unlike binary (0↔1 symmetric), ternary transitions
 * have different delays depending on source/target states.
 *
 * Key transitions modeled:
 *   - 0→1 (Depleted → Partial): RM must transition to LRS, slow
 *   - 1→2 (Partial → Accumulated): channel fully opens, medium
 *   - 0→2 (Depleted → Accumulated): bypass partial, fast
 *   - 2→1 (Accumulated → Partial): controlled de-accumulation, slow
 *   - 2→0 (Accumulated → Depleted): full discharge, fast
 *   - 1→0 (Partial → Depleted): RM transitions to HRS, medium
 *
 * Applications:
 *   - Timing analysis for ternary critical paths
 *   - Clock period computation for worst-case chains
 *   - PDP (Power-Delay Product) estimation
 *   - Gate chain timing simulation
 *
 * @see INCREASE_FUNCTIONAL_UTILITY.md § Propagation Delay Variance
 * @see dlfet_sim.h for device-level simulation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_PROP_DELAY_H
#define SET6_PROP_DELAY_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants (picoseconds) ========================================== */

/** Propagation delays per transition (ps at nominal Vdd=0.8V, 25°C) */
#define PDELAY_0_TO_1_PS    120   /**< Depleted → Partial (RM LRS setup) */
#define PDELAY_1_TO_2_PS     80   /**< Partial → Accumulated */
#define PDELAY_0_TO_2_PS     60   /**< Depleted → Accumulated (direct) */
#define PDELAY_2_TO_1_PS    130   /**< Accumulated → Partial (controlled) */
#define PDELAY_1_TO_0_PS     90   /**< Partial → Depleted (RM HRS) */
#define PDELAY_2_TO_0_PS     55   /**< Accumulated → Depleted (discharge) */
#define PDELAY_NO_CHANGE_PS   0   /**< Same state — no transition */

/** Temperature coefficient (+ps per 10°C above 25°C) */
#define PDELAY_TEMP_COEFF_PS  5

/** Voltage coefficient (+ps per 100mV below nominal 800mV) */
#define PDELAY_VOLT_COEFF_PS  15

/** Maximum chain length for analysis */
#define PDELAY_MAX_CHAIN     128

/* ==== Structures ======================================================= */

/**
 * @brief Transition type enumeration.
 */
typedef enum {
    PDELAY_TRANS_0_1,  /**< 0 → 1 */
    PDELAY_TRANS_1_2,  /**< 1 → 2 */
    PDELAY_TRANS_0_2,  /**< 0 → 2 */
    PDELAY_TRANS_2_1,  /**< 2 → 1 */
    PDELAY_TRANS_1_0,  /**< 1 → 0 */
    PDELAY_TRANS_2_0,  /**< 2 → 0 */
    PDELAY_TRANS_NONE  /**< No change */
} pdelay_transition_t;

/**
 * @brief Operating conditions for delay adjustment.
 */
typedef struct {
    int   temperature_c;   /**< Temperature (°C), nominal = 25 */
    int   supply_mv;       /**< Supply voltage (mV), nominal = 800 */
    int   process_corner;  /**< -1=slow, 0=typical, +1=fast */
} pdelay_conditions_t;

/**
 * @brief Delay analysis result for a gate chain.
 */
typedef struct {
    int   total_delay_ps;      /**< Sum of all transition delays */
    int   worst_transition_ps; /**< Slowest single transition */
    int   best_transition_ps;  /**< Fastest single transition */
    int   num_transitions;     /**< Total transitions in chain */
    int   critical_index;      /**< Index of worst-case transition */
    int   max_frequency_mhz;   /**< Estimated max clock (1e6/total) */
} pdelay_analysis_t;

/* ==== API ============================================================== */

/**
 * @brief Initialize default operating conditions (25°C, 800mV, typical).
 */
void pdelay_conditions_init(pdelay_conditions_t *cond);

/**
 * @brief Get nominal propagation delay for a state transition.
 *
 * @param from  Source state (0, 1, or 2).
 * @param to    Target state (0, 1, or 2).
 * @return      Delay in picoseconds.
 */
int pdelay_get_nominal(int from, int to);

/**
 * @brief Get adjusted delay accounting for PVT conditions.
 *
 * @param from  Source state.
 * @param to    Target state.
 * @param cond  Operating conditions.
 * @return      Adjusted delay in picoseconds.
 */
int pdelay_get_adjusted(int from, int to, const pdelay_conditions_t *cond);

/**
 * @brief Classify a state transition.
 */
pdelay_transition_t pdelay_classify(int from, int to);

/**
 * @brief Analyze a gate chain for timing.
 *
 * Given a sequence of output states through a logic chain,
 * computes cumulative delay and identifies critical path.
 *
 * @param result  Output analysis result.
 * @param states  Array of unbalanced ternary states (0/1/2).
 * @param count   Number of states in chain.
 * @param cond    Operating conditions.
 * @return        0 on success, -1 on error.
 */
int pdelay_analyze_chain(pdelay_analysis_t *result,
                         const uint8_t *states, int count,
                         const pdelay_conditions_t *cond);

/**
 * @brief Compute Power-Delay Product for a transition.
 *
 * PDP = Energy(transition) × Delay(transition).
 * Returns value in atto-Joule × picoseconds (aJ·ps).
 *
 * @param from  Source state.
 * @param to    Target state.
 * @param cond  Operating conditions.
 * @return      PDP in aJ·ps.
 */
int pdelay_pdp(int from, int to, const pdelay_conditions_t *cond);

/**
 * @brief Compute minimum clock period for a given chain.
 *
 * Returns the worst-case path delay plus a setup margin.
 *
 * @param states  State chain.
 * @param count   Chain length.
 * @param cond    Operating conditions.
 * @return        Minimum clock period in picoseconds.
 */
int pdelay_min_clock_period(const uint8_t *states, int count,
                            const pdelay_conditions_t *cond);

#ifdef __cplusplus
}
#endif

#endif /* SET6_PROP_DELAY_H */
