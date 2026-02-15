/**
 * @file prop_delay.c
 * @brief seT6 Propagation Delay Variance Model — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/prop_delay.h"
#include <string.h>

/* ---- Internal --------------------------------------------------------- */

static int i_abs(int v) __attribute__((unused));
static int i_abs(int v) { return v < 0 ? -v : v; }

/** Nominal delay lookup by transition */
static int nominal_delays[3][3] = {
    /* from\to    0                1                2 */
    /* 0 */ { PDELAY_NO_CHANGE_PS, PDELAY_0_TO_1_PS, PDELAY_0_TO_2_PS },
    /* 1 */ { PDELAY_1_TO_0_PS,    PDELAY_NO_CHANGE_PS, PDELAY_1_TO_2_PS },
    /* 2 */ { PDELAY_2_TO_0_PS,    PDELAY_2_TO_1_PS, PDELAY_NO_CHANGE_PS }
};

/** Energy per transition (aJ estimate) */
static int energy_aj[3][3] = {
    /*       0    1    2 */
    /* 0 */ { 0,   5,   3 },
    /* 1 */ { 4,   0,   3 },
    /* 2 */ { 2,   6,   0 }
};

/* ---- API -------------------------------------------------------------- */

void pdelay_conditions_init(pdelay_conditions_t *cond) {
    cond->temperature_c  = 25;
    cond->supply_mv      = 800;
    cond->process_corner  = 0;
}

int pdelay_get_nominal(int from, int to) {
    if (from < 0 || from > 2 || to < 0 || to > 2)
        return 0;
    return nominal_delays[from][to];
}

int pdelay_get_adjusted(int from, int to, const pdelay_conditions_t *cond) {
    int base = pdelay_get_nominal(from, to);
    if (base == 0) return 0;

    /* Temperature adjustment: +5ps per 10°C above 25°C */
    int temp_adj = 0;
    if (cond->temperature_c > 25)
        temp_adj = ((cond->temperature_c - 25) * PDELAY_TEMP_COEFF_PS) / 10;
    else if (cond->temperature_c < 25)
        temp_adj = -((25 - cond->temperature_c) * PDELAY_TEMP_COEFF_PS) / 10;

    /* Voltage adjustment: +15ps per 100mV below 800mV */
    int volt_adj = 0;
    if (cond->supply_mv < 800)
        volt_adj = ((800 - cond->supply_mv) * PDELAY_VOLT_COEFF_PS) / 100;
    else if (cond->supply_mv > 800)
        volt_adj = -((cond->supply_mv - 800) * PDELAY_VOLT_COEFF_PS) / 100;

    /* Process corner: slow +20%, fast -15% */
    int corner_adj = 0;
    if (cond->process_corner < 0)
        corner_adj = base / 5;  /* +20% */
    else if (cond->process_corner > 0)
        corner_adj = -(base * 15) / 100;  /* -15% */

    int total = base + temp_adj + volt_adj + corner_adj;
    return (total > 0) ? total : 1; /* minimum 1ps */
}

pdelay_transition_t pdelay_classify(int from, int to) {
    if (from == to) return PDELAY_TRANS_NONE;
    if (from == 0 && to == 1) return PDELAY_TRANS_0_1;
    if (from == 1 && to == 2) return PDELAY_TRANS_1_2;
    if (from == 0 && to == 2) return PDELAY_TRANS_0_2;
    if (from == 2 && to == 1) return PDELAY_TRANS_2_1;
    if (from == 1 && to == 0) return PDELAY_TRANS_1_0;
    if (from == 2 && to == 0) return PDELAY_TRANS_2_0;
    return PDELAY_TRANS_NONE;
}

int pdelay_analyze_chain(pdelay_analysis_t *result,
                         const uint8_t *states, int count,
                         const pdelay_conditions_t *cond) {
    if (!result || !states || count < 2 || count > PDELAY_MAX_CHAIN)
        return -1;

    memset(result, 0, sizeof(*result));
    result->best_transition_ps = 999999;
    result->num_transitions = count - 1;

    for (int i = 0; i < count - 1; i++) {
        int delay = pdelay_get_adjusted(states[i], states[i + 1], cond);

        result->total_delay_ps += delay;

        if (delay > result->worst_transition_ps) {
            result->worst_transition_ps = delay;
            result->critical_index = i;
        }
        if (delay < result->best_transition_ps && delay > 0) {
            result->best_transition_ps = delay;
        }
    }

    if (result->best_transition_ps == 999999)
        result->best_transition_ps = 0;

    /* Max frequency: 1 / total_delay (convert ps to MHz) */
    if (result->total_delay_ps > 0)
        result->max_frequency_mhz = 1000000 / result->total_delay_ps;
    else
        result->max_frequency_mhz = 0;

    return 0;
}

int pdelay_pdp(int from, int to, const pdelay_conditions_t *cond) {
    if (from < 0 || from > 2 || to < 0 || to > 2)
        return 0;

    int delay = pdelay_get_adjusted(from, to, cond);
    int e     = energy_aj[from][to];
    return delay * e;
}

int pdelay_min_clock_period(const uint8_t *states, int count,
                            const pdelay_conditions_t *cond) {
    pdelay_analysis_t result;
    if (pdelay_analyze_chain(&result, states, count, cond) != 0)
        return -1;

    /* Add 10% setup margin */
    return result.total_delay_ps + result.total_delay_ps / 10;
}
