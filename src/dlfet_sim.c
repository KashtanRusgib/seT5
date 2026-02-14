/**
 * @file dlfet_sim.c
 * @brief seT5 DLFET-RM Ternary Logic Gate Simulator — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/dlfet_sim.h"
#include <string.h>

/* ---- Helpers ---------------------------------------------------------- */

/** Clamp unbalanced ternary to {0, 1, 2} */
static uint8_t clamp3(int v) {
    if (v < 0) return 0;
    if (v > 2) return 2;
    return (uint8_t)v;
}

/* ---- API -------------------------------------------------------------- */

void dlfet_sim_init(dlfet_sim_state_t *state) {
    memset(state, 0, sizeof(*state));
}

void dlfet_device_init(dlfet_device_t *dev) {
    dev->vth_mv  = DLFET_VTH_NOM_MV;
    dev->vgs_mv  = 0;
    dev->vds_mv  = 0;
    dev->rm_state = RM_LRS;
    dev->channel  = DLFET_DEPLETED;
    dev->ids_na   = 0;
    dev->vout_mv  = 0;
}

/* ---- Unbalanced ternary gates ----------------------------------------- */

uint8_t dlfet_tnot(dlfet_sim_state_t *state, uint8_t a) {
    state->total_gates++;
    state->total_transitions++;
    state->energy_aj += DLFET_PDP_TNOT_AJ;
    state->prop_delay_ps = 30;

    /* Standard Ternary Inverter: 0→2, 1→1, 2→0 */
    switch (a) {
        case 0: return 2;
        case 1: return 1;
        case 2: return 0;
        default: return 1;
    }
}

uint8_t dlfet_tnand(dlfet_sim_state_t *state, uint8_t a, uint8_t b) {
    state->total_gates++;
    state->total_transitions++;
    state->energy_aj += DLFET_PDP_TNAND_AJ;
    state->prop_delay_ps = 55;

    /*
     * DLFET-RM TNAND truth table (Samsung patent):
     * (0,0)→2  (0,1)→2  (0,2)→2
     * (1,0)→2  (1,1)→1  (1,2)→1
     * (2,0)→2  (2,1)→1  (2,2)→0
     */
    if (a == 0 || b == 0)       return 2;
    if (a == 2 && b == 2)       return 0;
    if (a == 1 || b == 1)       return 1;
    /* (2,1) or (1,2) */
    return 1;
}

uint8_t dlfet_tnor(dlfet_sim_state_t *state, uint8_t a, uint8_t b) {
    state->total_gates++;
    state->total_transitions++;
    state->energy_aj += DLFET_PDP_TNAND_AJ; /* similar cost */
    state->prop_delay_ps = 55;

    /*
     * TNOR: NOR = NOT(OR) in ternary
     * OR = max(a, b), then NOT
     * (0,0)→2  (0,1)→1  (0,2)→0
     * (1,0)→1  (1,1)→1  (1,2)→0
     * (2,0)→0  (2,1)→0  (2,2)→0
     */
    uint8_t or_val = (a > b) ? a : b;
    return dlfet_tnot(state, or_val);
}

uint8_t dlfet_tand(dlfet_sim_state_t *state, uint8_t a, uint8_t b) {
    /* TAND = NOT(NAND(a,b)) */
    return dlfet_tnot(state, dlfet_tnand(state, a, b));
}

uint8_t dlfet_tor(dlfet_sim_state_t *state, uint8_t a, uint8_t b) {
    /* TOR = NOT(NOR(a,b)) */
    return dlfet_tnot(state, dlfet_tnor(state, a, b));
}

uint8_t dlfet_tmin(dlfet_sim_state_t *state, uint8_t a, uint8_t b) {
    state->total_gates++;
    return (a < b) ? a : b;
}

uint8_t dlfet_tmax(dlfet_sim_state_t *state, uint8_t a, uint8_t b) {
    state->total_gates++;
    return (a > b) ? a : b;
}

/* ---- Arithmetic ------------------------------------------------------- */

void dlfet_ternary_half_adder(dlfet_sim_state_t *state,
                               uint8_t a, uint8_t b,
                               uint8_t *sum, uint8_t *carry) {
    state->total_gates++;
    state->total_transitions++;
    state->energy_aj += DLFET_PDP_TNAND_AJ * 3; /* ~3 gate equivalent */

    int s = (int)a + (int)b;
    *sum   = clamp3(s % 3);
    *carry = clamp3(s / 3);
}

void dlfet_ternary_full_adder(dlfet_sim_state_t *state,
                               uint8_t a, uint8_t b, uint8_t cin,
                               uint8_t *sum, uint8_t *cout) {
    state->total_gates++;
    state->total_transitions++;
    state->energy_aj += DLFET_PDP_TFA_AJ;
    state->prop_delay_ps = 85;

    int s = (int)a + (int)b + (int)cin;
    *sum  = clamp3(s % 3);
    *cout = clamp3(s / 3);
}

uint8_t dlfet_ternary_add(dlfet_sim_state_t *state,
                           const uint8_t *a, const uint8_t *b,
                           uint8_t *result, int width) {
    uint8_t carry = 0;
    for (int i = 0; i < width; i++) {
        uint8_t s, c;
        dlfet_ternary_full_adder(state, a[i], b[i], carry, &s, &c);
        result[i] = s;
        carry = c;
    }
    return carry;
}

/* ---- Performance metrics ---------------------------------------------- */

int dlfet_pdp_estimate(int gate_type) {
    switch (gate_type) {
        case 0: return DLFET_PDP_TNOT_AJ;
        case 1: return DLFET_PDP_TNAND_AJ;
        case 2: return DLFET_PDP_TNAND_AJ; /* TNOR similar */
        case 3: return DLFET_PDP_TNAND_AJ * 3; /* THA */
        case 4: return DLFET_PDP_TFA_AJ;
        default: return 0;
    }
}

int dlfet_noise_margin(int vth_mv) {
    /* NM = V_mid - Vth (should be positive for stability) */
    /* Plus margin from RM clamping */
    int nm = DLFET_V_MID_MV - vth_mv + DLFET_NOISE_MARGIN_MV;
    return nm;
}

void dlfet_sim_stats(const dlfet_sim_state_t *state,
                     int *gates, int *transitions, int *energy_aj) {
    if (gates)       *gates       = state->total_gates;
    if (transitions) *transitions = state->total_transitions;
    if (energy_aj)   *energy_aj   = state->energy_aj;
}
