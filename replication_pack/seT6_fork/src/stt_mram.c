/**
 * @file stt_mram.c
 * @brief seT6 STT-MRAM Ternary Memory Interface — Implementation
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/stt_mram.h"
#include <string.h>

/* ---- Internal helpers ------------------------------------------------- */

/** Map balanced trit {-1,0,+1} to MTJ state {0,1,2} */
static mtj_state_t balanced_to_mtj(trit t) {
    return (mtj_state_t)((int)t + 1);
}

/** Map MTJ state {0,1,2} to balanced trit {-1,0,+1} */
static trit mtj_to_balanced(mtj_state_t s) {
    return (trit)((int)s - 1);
}

/** Get nominal resistance for a state */
static int nominal_r(mtj_state_t s) {
    switch (s) {
        case MTJ_STATE_0: return MRAM_R_LOW_X10;
        case MTJ_STATE_1: return MRAM_R_MID_X10;
        case MTJ_STATE_2: return MRAM_R_HIGH_X10;
        default:          return MRAM_R_MID_X10;
    }
}

/** Sense a cell — determine state from resistance */
static mtj_state_t sense_cell(const mram_cell_t *cell) {
    if (cell->resistance_x10 < (MRAM_R_LOW_X10 + MRAM_R_MID_X10) / 2)
        return MTJ_STATE_0;
    else if (cell->resistance_x10 < (MRAM_R_MID_X10 + MRAM_R_HIGH_X10) / 2)
        return MTJ_STATE_1;
    else
        return MTJ_STATE_2;
}

/* ---- Public API ------------------------------------------------------- */

int mram_init(mram_array_t *arr, int rows, int cols) {
    if (!arr || rows <= 0 || cols <= 0 ||
        rows > MRAM_MAX_ROWS || cols > MRAM_MAX_COLS)
        return -1;

    memset(arr, 0, sizeof(*arr));
    arr->rows = rows;
    arr->cols = cols;
    arr->total_cells = rows * cols;
    arr->ecs_status = MRAM_ECS_STABLE;

    /* Initialize all cells to State 0 (Logic 0, Low Resistance) */
    for (int i = 0; i < arr->total_cells; i++) {
        arr->cells[i].state = MTJ_STATE_0;
        arr->cells[i].resistance_x10 = MRAM_R_LOW_X10;
        arr->cells[i].write_count = 0;
    }

    return 0;
}

int mram_write_trit(mram_array_t *arr, int row, int col, trit val) {
    if (!arr || row < 0 || row >= arr->rows || col < 0 || col >= arr->cols)
        return -1;

    int idx = row * arr->cols + col;
    mtj_state_t target = balanced_to_mtj(val);

    arr->cells[idx].state = target;
    arr->cells[idx].resistance_x10 = nominal_r(target);
    arr->cells[idx].write_count++;
    arr->writes++;

    return 0;
}

trit mram_read_trit(mram_array_t *arr, int row, int col) {
    if (!arr || row < 0 || row >= arr->rows || col < 0 || col >= arr->cols)
        return TRIT_UNKNOWN;

    int idx = row * arr->cols + col;
    arr->reads++;

    /* Sense the cell via resistance thresholds */
    mtj_state_t sensed = sense_cell(&arr->cells[idx]);
    return mtj_to_balanced(sensed);
}

uint8_t mram_pack_trits(const trit *trits) {
    /* 5 trits → byte: val = Σ (trit[i]+1) × 3^i, range [0..242] */
    int val = 0;
    int base = 1;
    for (int i = 0; i < MRAM_TRITS_PER_BYTE; i++) {
        val += ((int)trits[i] + 1) * base;
        base *= 3;
    }
    return (uint8_t)(val < MRAM_PACK_BASE ? val : MRAM_PACK_BASE - 1);
}

void mram_unpack_trits(uint8_t byte, trit *trits) {
    int val = (int)byte;
    for (int i = 0; i < MRAM_TRITS_PER_BYTE; i++) {
        trits[i] = (trit)((val % 3) - 1);
        val /= 3;
    }
}

mram_result_t mram_read_packed(mram_array_t *arr, int start, uint8_t *out) {
    mram_result_t res = {0, 0, 0};
    if (!arr || !out || start < 0 ||
        start + MRAM_TRITS_PER_BYTE > arr->total_cells) {
        res.status = -1;
        return res;
    }

    trit trits[MRAM_TRITS_PER_BYTE];
    for (int i = 0; i < MRAM_TRITS_PER_BYTE; i++) {
        int idx = start + i;
        arr->reads++;
        mtj_state_t sensed = sense_cell(&arr->cells[idx]);

        /* Check for drift → ECS */
        if (sensed != arr->cells[idx].state) {
            res.ecs_triggered = 1;
            arr->drift_events++;
        }
        trits[i] = mtj_to_balanced(sensed);
    }

    *out = mram_pack_trits(trits);
    res.trits_transferred = MRAM_TRITS_PER_BYTE;
    return res;
}

mram_result_t mram_write_packed(mram_array_t *arr, int start, uint8_t byte) {
    mram_result_t res = {0, 0, 0};
    if (!arr || start < 0 ||
        start + MRAM_TRITS_PER_BYTE > arr->total_cells) {
        res.status = -1;
        return res;
    }

    trit trits[MRAM_TRITS_PER_BYTE];
    mram_unpack_trits(byte, trits);

    for (int i = 0; i < MRAM_TRITS_PER_BYTE; i++) {
        int idx = start + i;
        mtj_state_t target = balanced_to_mtj(trits[i]);
        arr->cells[idx].state = target;
        arr->cells[idx].resistance_x10 = nominal_r(target);
        arr->cells[idx].write_count++;
        arr->writes++;
    }

    res.trits_transferred = MRAM_TRITS_PER_BYTE;
    return res;
}

int mram_xor_trit(mram_array_t *arr, int addr, trit val) {
    if (!arr || addr < 0 || addr >= arr->total_cells)
        return -1;

    /* Ternary XOR at sense-amplifier level: (a + b) mod 3 in balanced */
    trit current = mtj_to_balanced(arr->cells[addr].state);
    int sum = (int)current + (int)val;
    if (sum >  1) sum -= 3;
    if (sum < -1) sum += 3;

    mtj_state_t target = balanced_to_mtj((trit)sum);
    arr->cells[addr].state = target;
    arr->cells[addr].resistance_x10 = nominal_r(target);
    arr->xor_ops++;

    return 0;
}

int mram_stabilize(mram_array_t *arr, int addr) {
    if (!arr) return -1;

    int count = 0;
    int lo = (addr < 0) ? 0 : addr;
    int hi = (addr < 0) ? arr->total_cells : addr + 1;

    for (int i = lo; i < hi && i < arr->total_cells; i++) {
        int nom = nominal_r(arr->cells[i].state);
        if (arr->cells[i].resistance_x10 != nom) {
            arr->cells[i].resistance_x10 = nom;
            count++;
        }
    }

    arr->stab_ops++;
    arr->ecs_status = MRAM_ECS_STABLE;
    arr->ecs_recal_count = 0;
    return count;
}

int mram_ecs_scan(mram_array_t *arr) {
    if (!arr) return -1;

    int corrected = 0;
    for (int i = 0; i < arr->total_cells; i++) {
        int nom = nominal_r(arr->cells[i].state);
        int drift = arr->cells[i].resistance_x10 - nom;
        if (drift < 0) drift = -drift;

        if (drift > MRAM_ECS_DRIFT_THRESHOLD_X10) {
            /* Check if drift changed the sensed state */
            mtj_state_t sensed = sense_cell(&arr->cells[i]);
            if (sensed != arr->cells[i].state) {
                /* Recalibrate */
                arr->cells[i].resistance_x10 = nom;
                corrected++;
                arr->ecs_recal_count++;
                arr->drift_events++;
            }
        }
    }

    if (arr->ecs_recal_count > MRAM_ECS_MAX_RECAL) {
        arr->ecs_status = MRAM_ECS_FAILED;
        arr->guardian_fails++;
        return -1;
    }

    arr->ecs_status = (corrected > 0) ? MRAM_ECS_RECALIBRATING : MRAM_ECS_STABLE;
    return corrected;
}

int mram_nominal_resistance(mtj_state_t state) {
    return nominal_r(state);
}

int mram_inject_drift(mram_array_t *arr, int addr, int drift) {
    if (!arr || addr < 0 || addr >= arr->total_cells)
        return -1;

    arr->cells[addr].resistance_x10 += drift;
    return 0;
}

const char *mram_ecs_status_str(mram_ecs_status_t s) {
    switch (s) {
        case MRAM_ECS_STABLE:        return "STABLE";
        case MRAM_ECS_DRIFTING:      return "DRIFTING";
        case MRAM_ECS_RECALIBRATING: return "RECALIBRATING";
        case MRAM_ECS_FAILED:        return "FAILED";
        default:                     return "UNKNOWN";
    }
}
