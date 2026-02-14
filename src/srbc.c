/**
 * @file srbc.c
 * @brief seT5 Self-Referential Bias Calibration — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/srbc.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

static int i_abs(int v) { return v < 0 ? -v : v; }

static int clamp_int(int v, int lo, int hi) {
    if (v < lo) return lo;
    if (v > hi) return hi;
    return v;
}

/* ---- API -------------------------------------------------------------- */

void srbc_init(srbc_state_t *state) {
    memset(state, 0, sizeof(*state));

    state->v_target_mv   = SRBC_V_TARGET_MV;
    state->v_current_mv  = SRBC_V_TARGET_MV;
    state->supply_mv     = 800; /* nominal Vdd */
    state->temperature_mc = 25000; /* 25°C in milli-Celsius */
    state->process_corner = 0;   /* typical */
    state->status = SRBC_STABLE;
    state->snm_mv = SRBC_MAX_DRIFT_MV * 2;

    /* Initialize reference cells */
    state->num_ref_cells = SRBC_NUM_REF_CELLS;
    for (int i = 0; i < SRBC_NUM_REF_CELLS; i++) {
        state->ref_cells[i].vth_nominal_mv = 350;
        state->ref_cells[i].vth_actual_mv  = 350;
        state->ref_cells[i].leakage_na     = 10;
        state->ref_cells[i].temperature_mc = 25000;
        state->ref_cells[i].drift_mv       = 0;
    }
}

srbc_status_t srbc_tick(srbc_state_t *state) {
    state->ticks++;

    /* Read reference cells, compute average drift */
    int total_drift = 0;
    for (int i = 0; i < state->num_ref_cells; i++) {
        total_drift += state->ref_cells[i].drift_mv;
    }
    int avg_drift = total_drift / state->num_ref_cells;

    /* Apply thermal drift to current voltage */
    int thermal_offset = ((state->temperature_mc - 25000) * SRBC_THERMAL_COEFF_UV)
                         / 1000 / 1000; /* µV/°C → mV */
    state->v_current_mv = state->v_target_mv + avg_drift + thermal_offset;

    /* Compute SNM */
    int deviation = i_abs(state->v_current_mv - state->v_target_mv);
    state->snm_mv = SRBC_MAX_DRIFT_MV * 2 - deviation;

    /* Check if recalibration needed */
    if (deviation > SRBC_MAX_DRIFT_MV * 3) {
        /* Severe — tamper or catastrophic drift */
        state->status = SRBC_TAMPERED;
        state->tamper_events++;
    } else if (deviation > SRBC_MAX_DRIFT_MV) {
        /* Needs active recalibration */
        state->status = SRBC_RECALIBRATING;

        /* Apply negative feedback correction */
        int correction = -(avg_drift + thermal_offset);
        correction = clamp_int(correction, -SRBC_MAX_DRIFT_MV, SRBC_MAX_DRIFT_MV);

        /* Apply correction to all reference cells */
        for (int i = 0; i < state->num_ref_cells; i++) {
            state->ref_cells[i].drift_mv += correction;
            state->ref_cells[i].vth_actual_mv =
                state->ref_cells[i].vth_nominal_mv + state->ref_cells[i].drift_mv;
        }

        state->correction_mv = correction;
        state->v_current_mv += correction;
        state->total_calibrations++;

        /* Log event */
        if (state->history_count < SRBC_MAX_HISTORY) {
            srbc_cal_event_t *ev = &state->history[state->history_count++];
            ev->timestamp      = state->ticks;
            ev->drift_before_mv = avg_drift;
            ev->correction_mv  = correction;
            ev->temperature_mc = state->temperature_mc;
            ev->status         = SRBC_RECALIBRATING;
        }

        /* Recheck after correction */
        deviation = i_abs(state->v_current_mv - state->v_target_mv);
        if (deviation <= SRBC_MAX_DRIFT_MV) {
            state->status = SRBC_STABLE;
        }
    } else if (deviation > SRBC_MAX_DRIFT_MV / 2) {
        state->status = SRBC_DRIFTING;
    } else {
        state->status = SRBC_STABLE;
    }

    /* Track stability */
    if (state->status == SRBC_STABLE)
        state->stable_ticks++;
    state->stability_pct = (state->ticks > 0)
        ? (state->stable_ticks * 100) / state->ticks : 100;

    return state->status;
}

void srbc_apply_thermal(srbc_state_t *state, int delta_mc) {
    state->temperature_mc += delta_mc;

    /* Apply thermal drift to reference cells */
    int drift_uv = (delta_mc * SRBC_THERMAL_COEFF_UV) / 1000; /* mC × µV/°C */
    int drift_mv = drift_uv / 1000;

    for (int i = 0; i < state->num_ref_cells; i++) {
        state->ref_cells[i].drift_mv += drift_mv;
        state->ref_cells[i].temperature_mc = state->temperature_mc;
        state->ref_cells[i].vth_actual_mv =
            state->ref_cells[i].vth_nominal_mv + state->ref_cells[i].drift_mv;
    }
}

void srbc_apply_voltage(srbc_state_t *state, int new_vdd_mv) {
    int delta = new_vdd_mv - state->supply_mv;
    state->supply_mv = new_vdd_mv;

    /* V_target scales with supply */
    state->v_target_mv = new_vdd_mv / 2;

    /* Supply variation affects reference cells */
    int ref_drift = delta / 10; /* 10% coupling */
    for (int i = 0; i < state->num_ref_cells; i++)
        state->ref_cells[i].drift_mv += ref_drift;
}

int srbc_inject_fault(srbc_state_t *state, int inject_mv) {
    /* Apply fault to all reference cells */
    for (int i = 0; i < state->num_ref_cells; i++)
        state->ref_cells[i].drift_mv += inject_mv;

    /* Check if injection exceeds tamper threshold */
    if (i_abs(inject_mv) > SRBC_MAX_DRIFT_MV * 2) {
        state->status = SRBC_TAMPERED;
        state->tamper_events++;
        return 1; /* tamper detected */
    }

    return 0;
}

int srbc_get_snm(const srbc_state_t *state) {
    return state->snm_mv;
}

int srbc_get_stability(const srbc_state_t *state) {
    return state->stability_pct;
}

void srbc_reset_refs(srbc_state_t *state) {
    for (int i = 0; i < state->num_ref_cells; i++) {
        state->ref_cells[i].vth_actual_mv = state->ref_cells[i].vth_nominal_mv;
        state->ref_cells[i].drift_mv = 0;
    }
    state->v_current_mv = state->v_target_mv;
    state->status = SRBC_STABLE;
    state->snm_mv = SRBC_MAX_DRIFT_MV * 2;
}

trit srbc_voltage_to_trit(int voltage_mv) {
    int center = SRBC_V_TARGET_MV;
    int margin = SRBC_MAX_DRIFT_MV;

    if (voltage_mv < center - margin)
        return TRIT_FALSE;
    else if (voltage_mv > center + margin)
        return TRIT_TRUE;
    else
        return TRIT_UNKNOWN; /* within stable "1" window → middle state */
}
