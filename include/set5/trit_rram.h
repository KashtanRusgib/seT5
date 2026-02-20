/**
 * @file trit_rram.h
 * @brief seT6 — Multi-State RRAM (Resistive RAM) for Ternary Storage
 *
 * Models the multi-state RRAM (memristor) platform from Steven Bos's
 * 2024 PhD thesis, Chapter 3 and Paper A:
 *   "uMemristorToolbox: Open source framework to control memristors
 *   in Unity for ternary applications" (ISMVL 2020).
 *
 * Physical properties:
 *   • Each memristor cell can hold up to 96 stable resistance states
 *     (Stathopoulos et al. 2017 — 6.5 bits/cell)
 *   • In seT6 context: 3 primary states per cell (ternary storage)
 *   • Cells as small as a few nm² (Pi et al. 2018)
 *   • Non-volatile: no power needed to retain state
 *   • CNTFETs enable low-power ternary PUF circuits (He et al. 2018)
 *
 * Resistance state encoding (balanced ternary):
 *   HRS (High Resistance State)  →  TRIT_FALSE  (-1)
 *   MRS (Middle Resistance State) → TRIT_UNKNOWN (0)
 *   LRS (Low Resistance State)   →  TRIT_TRUE   (+1)
 *
 * DLFET-RM integration (INCREASE_FUNCTIONAL_UTILITY.md reference):
 *   The RM element acts as an "electronic gauge block" clamping the
 *   output to VDD/2 in the intermediate state (state 1) without the
 *   thermal runaway seen in CMOS voltage-division approaches.
 *   Current in state "1" is stabilised at ~nA vs µA leakage in CMOS.
 *
 * Fault model:
 *   RRAM cells can degrade; a degraded cell is modelled as STUCK_AT
 *   or DRIFT (resistance moves toward LRS or HRS over time).
 *   TMR (trit_tmr.h) masks single-cell faults.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_RRAM_H
#define SET6_TRIT_RRAM_H

#include "set5/trit.h"
#include <stdint.h>
#include <stdbool.h>

#ifdef __cplusplus
extern "C"
{
#endif

    /* ============================================================
     * Section 1: Resistance state and cell model
     * ============================================================ */

    /**
     * @brief RRAM resistance state (3 primary levels for ternary).
     */
    typedef enum
    {
        RRAM_HRS = 0,  /* High Resistance — FALSE (-1) */
        RRAM_MRS = 1,  /* Mid  Resistance — UNKNOWN (0) */
        RRAM_LRS = 2,  /* Low  Resistance — TRUE (+1)  */
        RRAM_FAULT = 3 /* Degraded / stuck — maps to UNKNOWN on read */
    } rram_state_t;

    /**
     * @brief Convert an RRAM resistance state to a K₃ trit.
     *
     * @param rs  RRAM state.
     * @return    K₃ trit: -1, 0, or +1.  FAULT → TRIT_UNKNOWN.
     */
    static inline int8_t rram_to_trit(rram_state_t rs)
    {
        switch (rs)
        {
        case RRAM_HRS:
            return TRIT_FALSE;
        case RRAM_MRS:
            return TRIT_UNKNOWN;
        case RRAM_LRS:
            return TRIT_TRUE;
        default:
            return TRIT_UNKNOWN; /* RRAM_FAULT: conservative */
        }
    }

    /**
     * @brief Convert a K₃ trit to an RRAM resistance state.
     *
     * @param t  K₃ trit (-1, 0, +1).
     * @return   RRAM state (HRS / MRS / LRS).
     */
    static inline rram_state_t trit_to_rram(int8_t t)
    {
        if (t > 0)
            return RRAM_LRS;
        if (t < 0)
            return RRAM_HRS;
        return RRAM_MRS;
    }

    /**
     * @brief Model of a single RRAM cell.
     */
    typedef struct
    {
        rram_state_t state;    /* current resistance state */
        uint8_t write_cycles;  /* write endurance counter (<255) */
        bool stuck;            /* true if cell is permanently stuck */
        rram_state_t stuck_at; /* state when stuck */
    } rram_cell_t;

    /**
     * @brief Initialise an RRAM cell to HRS (FALSE) state.
     */
    static inline void rram_cell_init(rram_cell_t *cell)
    {
        if (!cell)
            return;
        cell->state = RRAM_HRS;
        cell->write_cycles = 0;
        cell->stuck = false;
        cell->stuck_at = RRAM_HRS;
    }

    /**
     * @brief Write a trit value to an RRAM cell.
     *
     * If the cell is stuck, the write is rejected (fault preserved).
     * write_cycles is incremented; endurance limit is modelled as 200
     * write cycles before marking stuck (simplified model).
     *
     * @param cell  RRAM cell to write.
     * @param t     K₃ trit to store (-1, 0, or +1).
     * @return      true if write succeeded; false if cell is stuck.
     */
    static inline bool rram_cell_write(rram_cell_t *cell, int8_t t)
    {
        if (!cell)
            return false;
        if (cell->stuck)
            return false; /* stuck-at fault */
        cell->state = trit_to_rram(t);
        cell->write_cycles++;
        if (cell->write_cycles >= 200)
        { /* endurance degradation */
            cell->stuck = true;
            cell->stuck_at = cell->state;
        }
        return true;
    }

    /**
     * @brief Read the trit value from an RRAM cell.
     *
     * A stuck cell returns RRAM_FAULT → TRIT_UNKNOWN (conservative).
     *
     * @param cell  RRAM cell to read.
     * @return      K₃ trit (-1, 0, or +1); TRIT_UNKNOWN on fault.
     */
    static inline int8_t rram_cell_read(const rram_cell_t *cell)
    {
        if (!cell)
            return TRIT_UNKNOWN;
        if (cell->stuck)
            return TRIT_UNKNOWN; /* fault → unknown (conservative) */
        return rram_to_trit(cell->state);
    }

    /* ============================================================
     * Section 2: RRAM array (multi-trit block storage)
     * ============================================================ */

#define RRAM_ARRAY_MAX_CELLS 128 /* configurable array size */

    /**
     * @brief An RRAM array of up to RRAM_ARRAY_MAX_CELLS ternary cells.
     */
    typedef struct
    {
        rram_cell_t cells[RRAM_ARRAY_MAX_CELLS];
        uint32_t num_cells;
    } rram_array_t;

    /**
     * @brief Initialise an RRAM array.
     *
     * @param arr       Array to initialise.
     * @param num_cells Number of cells to activate (1..RRAM_ARRAY_MAX_CELLS).
     */
    static inline void rram_array_init(rram_array_t *arr, uint32_t num_cells)
    {
        if (!arr || num_cells == 0 || num_cells > RRAM_ARRAY_MAX_CELLS)
            return;
        arr->num_cells = num_cells;
        for (uint32_t i = 0; i < num_cells; i++)
            rram_cell_init(&arr->cells[i]);
    }

    /**
     * @brief Write a trit to cell index addr in the RRAM array.
     *
     * @param arr   RRAM array.
     * @param addr  Cell index.
     * @param t     Trit to write.
     * @return      true on success; false if out-of-range or cell stuck.
     */
    static inline bool rram_write(rram_array_t *arr, uint32_t addr, int8_t t)
    {
        if (!arr || addr >= arr->num_cells)
            return false;
        return rram_cell_write(&arr->cells[addr], t);
    }

    /**
     * @brief Read a trit from cell index addr in the RRAM array.
     *
     * @param arr   RRAM array.
     * @param addr  Cell index.
     * @return      Stored trit, or TRIT_UNKNOWN on fault/out-of-range.
     */
    static inline int8_t rram_read(const rram_array_t *arr, uint32_t addr)
    {
        if (!arr || addr >= arr->num_cells)
            return TRIT_UNKNOWN;
        return rram_cell_read(&arr->cells[addr]);
    }

    /**
     * @brief Count the number of fault (stuck) cells in the array.
     *
     * @param arr  RRAM array.
     * @return     Number of stuck cells.
     */
    static inline uint32_t rram_fault_count(const rram_array_t *arr)
    {
        if (!arr)
            return 0;
        uint32_t count = 0;
        for (uint32_t i = 0; i < arr->num_cells; i++)
            if (arr->cells[i].stuck)
                count++;
        return count;
    }

    /* ============================================================
     * Section 3: Multi-state encoding (96 levels)
     *
     * For high-density applications (Stathopoulos et al. 2017) a single
     * memristor can encode up to 96 stable resistance states (6.5 bits).
     * In seT6, we expose a simplified API for up to 8 states (3 bits).
     * The physical 96-state variant is used in solid-state drives and is
     * not modelled in full here — only the ternary (3-state) and octal
     * (8-state) equivalents are provided.
     * ============================================================ */

#define RRAM_MAX_MULTISTATE_LEVELS 96

    /**
     * @brief Write a multi-state level (0..levels-1) to an RRAM cell.
     *
     * @param cell    RRAM cell (state is repurposed for enumeration).
     * @param level   Level index (0..levels-1).
     * @param levels  Total number of stable levels (3 for ternary, 8 for octal).
     * @return        true on success.
     */
    static inline bool rram_cell_write_level(rram_cell_t *cell,
                                             uint8_t level,
                                             uint8_t levels)
    {
        if (!cell || levels < 2 || levels > RRAM_MAX_MULTISTATE_LEVELS)
            return false;
        if (level >= levels)
            return false;
        if (cell->stuck)
            return false;
        /* Map level to one of 3 resistance states for simulation */
        if (level == 0)
            cell->state = RRAM_HRS;
        else if (level == levels - 1)
            cell->state = RRAM_LRS;
        else
            cell->state = RRAM_MRS;
        cell->write_cycles++;
        return true;
    }

#ifdef __cplusplus
}
#endif
#endif /* SET6_TRIT_RRAM_H */
