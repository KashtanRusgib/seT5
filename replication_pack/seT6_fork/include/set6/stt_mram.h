/**
 * @file stt_mram.h
 * @brief seT6 STT-MRAM Ternary Memory Interface — Out-of-Band Memory Module
 *
 * Non-volatile ternary storage using Multi-Level Cell (MLC) STT-MRAM with
 * Biaxial Magnetic Tunnel Junctions (MTJs).  Three distinct resistance
 * states (R_L, R_M, R_H) map directly to trit values {0, 1, 2} (unbalanced)
 * or {-1, 0, +1} (balanced).
 *
 * The module interfaces with the seT6 microkernel through the existing IPC
 * and MMU abstraction layers, treating the STT-MRAM array as a high-density,
 * non-volatile "External Page Frame." **Zero modification to the microkernel.**
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_STT_MRAM_H
#define SET6_STT_MRAM_H

#include "set6/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Physical Constants ================================================ */

/** Resistance states for Biaxial MTJ — Ohm equivalents (×10 for precision) */
#define MRAM_R_LOW_X10       50       /* Parallel (P): ~5 kΩ  → State 0  */
#define MRAM_R_MID_X10       120      /* Orthogonal (90°): ~12 kΩ → State 1 */
#define MRAM_R_HIGH_X10      250      /* Anti-Parallel (AP): ~25 kΩ → State 2 */

/** Sense amplifier thresholds (µA × 10) */
#define MRAM_TH_LOW_X10      100      /* Transition 0→1 boundary */
#define MRAM_TH_HIGH_X10     500      /* Transition 1→2 boundary */

/** Array geometry */
#define MRAM_MAX_ROWS        128
#define MRAM_MAX_COLS        128
#define MRAM_MAX_CELLS       (MRAM_MAX_ROWS * MRAM_MAX_COLS)

/** Trit packing: 5 trits → 8 bits (3^5=243, fits in uint8_t) */
#define MRAM_TRITS_PER_BYTE  5
#define MRAM_PACK_BASE       243

/** ECS (Error Correction & Stabilization) */
#define MRAM_ECS_DRIFT_THRESHOLD_X10  20   /* Max tolerable drift ×10 */
#define MRAM_ECS_MAX_RECAL    8             /* Max recalibrations before fail */
#define MRAM_GUARDIAN_OK      0
#define MRAM_GUARDIAN_DRIFT   1
#define MRAM_GUARDIAN_FAIL    2

/* ==== Types ============================================================= */

/** MTJ cell states (unbalanced ternary) */
typedef enum {
    MTJ_STATE_0 = 0,   /* Parallel — Low Resistance   */
    MTJ_STATE_1 = 1,   /* Orthogonal — Mid Resistance  */
    MTJ_STATE_2 = 2    /* Anti-Parallel — High Resistance */
} mtj_state_t;

/** Single STT-MRAM cell */
typedef struct {
    mtj_state_t  state;
    int          resistance_x10;    /* Current resistance ×10 Ω */
    int          write_count;       /* Endurance tracking */
} mram_cell_t;

/** ECS status */
typedef enum {
    MRAM_ECS_STABLE       = 0,
    MRAM_ECS_DRIFTING     = 1,
    MRAM_ECS_RECALIBRATING = 2,
    MRAM_ECS_FAILED       = 3
} mram_ecs_status_t;

/** STT-MRAM array */
typedef struct {
    mram_cell_t cells[MRAM_MAX_CELLS];
    int         rows;
    int         cols;
    int         total_cells;

    /* ECS state */
    mram_ecs_status_t ecs_status;
    int               ecs_recal_count;
    int               drift_events;
    int               guardian_fails;

    /* Statistics */
    int         reads;
    int         writes;
    int         xor_ops;
    int         stab_ops;
} mram_array_t;

/** Logic-in-Memory command results */
typedef struct {
    int  status;     /* 0 = success, <0 = error */
    int  trits_transferred;
    int  ecs_triggered;
} mram_result_t;

/* ==== LiM Command Set =================================================== */

/** Command IDs */
#define MEM_READ_T    0x01   /* Read 5 trits as 1 byte   */
#define MEM_WRITE_T   0x02   /* Write 1 byte as 5 trits  */
#define MEM_XOR_T     0x03   /* In-memory Ternary XOR    */
#define MEM_STAB_C    0x04   /* Recalibrate "1" State    */

/* ==== API ================================================================ */

/**
 * @brief Initialize an STT-MRAM array.
 * @param arr  Array to initialize.
 * @param rows Number of rows (≤ MRAM_MAX_ROWS).
 * @param cols Number of columns (≤ MRAM_MAX_COLS).
 * @return 0 on success, -1 on invalid geometry.
 */
int mram_init(mram_array_t *arr, int rows, int cols);

/**
 * @brief Write a trit value to a cell.
 * @param arr  Target array.
 * @param row  Row index.
 * @param col  Column index.
 * @param val  Trit value (-1, 0, +1 balanced; mapped to 0, 1, 2 internal).
 * @return 0 on success, -1 on error.
 */
int mram_write_trit(mram_array_t *arr, int row, int col, trit val);

/**
 * @brief Read a trit value from a cell.
 * @param arr  Source array.
 * @param row  Row index.
 * @param col  Column index.
 * @return Trit value (-1, 0, +1), or 0 on error (with ECS flag).
 */
trit mram_read_trit(mram_array_t *arr, int row, int col);

/**
 * @brief MEM_READ_T — Read 5 trits packed into 1 byte.
 * @param arr    Source array.
 * @param start  Starting linear index.
 * @param out    Output byte.
 * @return mram_result_t with status.
 */
mram_result_t mram_read_packed(mram_array_t *arr, int start, uint8_t *out);

/**
 * @brief MEM_WRITE_T — Write 1 byte as 5 trits.
 * @param arr    Target array.
 * @param start  Starting linear index.
 * @param byte   Input byte (0..242 for valid 5-trit values).
 * @return mram_result_t with status.
 */
mram_result_t mram_write_packed(mram_array_t *arr, int start, uint8_t byte);

/**
 * @brief MEM_XOR_T — In-memory ternary XOR at sense-amplifier level.
 *
 * Performs XOR on cells[addr] with given trit, zero CPU cycles (simulated).
 * @param arr   Target array.
 * @param addr  Linear cell address.
 * @param val   Trit to XOR with.
 * @return 0 on success, -1 on error.
 */
int mram_xor_trit(mram_array_t *arr, int addr, trit val);

/**
 * @brief MEM_STAB_C — Recalibrate the "1" state biasing.
 *
 * Adjusts biaxial MTJ biasing without CPU cycles; resets drift counters.
 * @param arr   Target array.
 * @param addr  Linear cell address (-1 for all cells).
 * @return Number of cells recalibrated.
 */
int mram_stabilize(mram_array_t *arr, int addr);

/**
 * @brief Run the ECS (Error Correction & Stabilization) loop.
 * @param arr  Target array.
 * @return Number of cells corrected; -1 if array failed.
 */
int mram_ecs_scan(mram_array_t *arr);

/**
 * @brief Trit packing: 5 trits → 1 byte (range 0..242).
 * @param trits Array of 5 trits (balanced: -1, 0, +1).
 * @return Packed byte value.
 */
uint8_t mram_pack_trits(const trit *trits);

/**
 * @brief Trit unpacking: 1 byte → 5 trits.
 * @param byte  Packed byte (0..242).
 * @param trits Output array of 5 trits (balanced).
 */
void mram_unpack_trits(uint8_t byte, trit *trits);

/**
 * @brief Get the nominal resistance for a given MTJ state.
 * @param state MTJ state (0, 1, or 2).
 * @return Resistance × 10 (Ohm).
 */
int mram_nominal_resistance(mtj_state_t state);

/**
 * @brief Inject drift fault for testing.
 * @param arr   Target array.
 * @param addr  Linear cell address.
 * @param drift Resistance drift ×10.
 * @return 0 on success, -1 on error.
 */
int mram_inject_drift(mram_array_t *arr, int addr, int drift);

/**
 * @brief Get ECS status string.
 */
const char *mram_ecs_status_str(mram_ecs_status_t s);

#ifdef __cplusplus
}
#endif

#endif /* SET6_STT_MRAM_H */
