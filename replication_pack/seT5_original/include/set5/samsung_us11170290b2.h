/**
 * @file samsung_us11170290b2.h
 * @brief seT5 Hardware Abstraction for Samsung US11170290B2 NAND Inference Chip
 *
 * Top-level header for Samsung's "Realization of neural networks with
 * ternary inputs and binary weights in NAND memory arrays" as described
 * in patent US11170290B2 (filed 2019-03-28, granted 2021-11-09,
 * assigned to Samsung Electronics Co., Ltd. via SanDisk Technologies LLC).
 *
 * Key patent architecture:
 *
 *   1. In-memory computing: multiply-accumulate within NAND flash
 *      arrays, eliminating the memory ↔ MAC bottleneck.
 *
 *   2. Unit synapse: pair of series-connected SLC (single-level cell)
 *      NAND memory cells on a common NAND string:
 *        - Weight +1: FG1=erased("1"), FG2=programmed("0")
 *        - Weight -1: FG1=programmed("0"), FG2=erased("1")
 *
 *   3. Input encoding via voltage patterns on word-line pairs (WL1, WL2):
 *        - Input -1: V1=Vpass, V2=Vread  (FG1 always conducts)
 *        - Input +1: V1=Vread, V2=Vpass  (FG2 always conducts)
 *        - Input  0: V1=Vread, V2=Vread  (only erased cells conduct)
 *      Where Vread distinguishes erased/programmed, Vpass passes both.
 *
 *   4. Output: sense amplifier detects NAND string conductivity:
 *        - Conducts → logic +1 (input matches weight)
 *        - Does not conduct → logic -1 (mismatch)
 *
 *   5. Dot-product accumulation via counter circuits:
 *        BNN: P = 2·CNT_out − S         (Eq. 1)
 *        TBN: P = 2·CNT_out − (S − Z)   (Eq. 2)
 *      Where S = vector size, Z = number of zero inputs, CNT_out =
 *      count of conducting synapses (excluding zero-input positions).
 *
 *   6. Zero Input Detection (ZID): NOR-gate circuit on word-line pairs
 *      detects when both WLs at Vread (zero input), generates BCC
 *      signal to exclude those synapse outputs from the counter.
 *
 *   7. Parallelism hierarchy:
 *        a. Sequential sensing within a block (one synapse per cycle)
 *        b. Multi-block: multi-bit sense amplifiers sense multiple
 *           blocks on the same plane concurrently
 *        c. Multi-plane: same weights stored across planes, different
 *           input vectors processed in parallel
 *        d. Plane pipelining: output of one plane/layer feeds as input
 *           to the next plane/layer for multi-layer DNN inference
 *
 * Mapping to seT5:
 *   seT5 uses balanced ternary {-1, 0, +1} (TRIT_FALSE/UNKNOWN/TRUE).
 *   Samsung TBN inputs are also {-1, 0, +1}, mapping directly.
 *   Samsung binary weights {-1, +1} are a subset of seT5 trit values.
 *
 * This header provides:
 *   - Patent reference constants
 *   - Weight and input encoding types
 *   - Voltage pattern mapping
 *   - Unit synapse emulation primitives
 *   - Chip capability and HAL state structures
 *   - Combined include for all Samsung sub-headers
 *
 * @see samsung_nand.h  — NAND array model and MMIO register map
 * @see samsung_tbn.h   — TBN inference engine interface
 * @see SAMSUNG_PATENT_US11170290B2.md — Full patent text
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SAMSUNG_US11170290B2_H
#define SET5_SAMSUNG_US11170290B2_H

#include "set5/trit.h"
#include "set5/trit_emu.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Patent Reference                                                      */
/* ===================================================================== */

#define SS_PATENT_ID            "US11170290B2"
#define SS_PATENT_ASSIGNEE      "Samsung Electronics Co., Ltd."
#define SS_PATENT_ORIG_ASSIGNEE "SanDisk Technologies LLC"
#define SS_PATENT_FILED         "2019-03-28"
#define SS_PATENT_GRANTED       "2021-11-09"
#define SS_PATENT_CLASS         "G06F7/5443"  /* Sum of products */
#define SS_PATENT_TITLE         \
    "Realization of neural networks with ternary inputs and " \
    "binary weights in NAND memory arrays"

/* ===================================================================== */
/* Binary Weight Type                                                    */
/* ===================================================================== */

/**
 * Samsung US11170290B2 uses binary weights: {-1, +1}.
 * Stored as a pair of SLC NAND cells in each unit synapse.
 *
 * Encoding in memory cell pair (FG1, FG2):
 *   Weight +1: FG1=erased("1"), FG2=programmed("0")
 *   Weight -1: FG1=programmed("0"), FG2=erased("1")
 *
 * We use int8_t for consistency with seT5 trit, but only ±1 valid.
 */
typedef int8_t ss_weight_t;

#define SS_WEIGHT_POS   ((ss_weight_t)+1)    /**< Weight = +1 */
#define SS_WEIGHT_NEG   ((ss_weight_t)-1)    /**< Weight = -1 */

/**
 * @brief Validate a binary weight value.
 * @return 1 if valid (+1 or -1), 0 otherwise.
 */
static inline int ss_weight_valid(ss_weight_t w)
{
    return (w == SS_WEIGHT_POS) || (w == SS_WEIGHT_NEG);
}

/* ===================================================================== */
/* Ternary Input Type (maps directly to seT5 trit)                       */
/* ===================================================================== */

/**
 * Samsung TBN inputs are ternary: {-1, 0, +1}.
 * These map directly to seT5 `trit` type without translation.
 *
 * For BNN mode, only {-1, +1} inputs are used (no zero).
 */
typedef trit ss_input_t;

#define SS_INPUT_NEG    TRIT_FALSE       /**< Input = -1 */
#define SS_INPUT_ZERO   TRIT_UNKNOWN     /**< Input =  0 (ternary only) */
#define SS_INPUT_POS    TRIT_TRUE        /**< Input = +1 */

/* ===================================================================== */
/* Voltage Levels and Patterns                                           */
/* ===================================================================== */

/**
 * Voltage levels applied to word lines (abstract representation).
 *
 * Vread: low voltage — only erased cells ("1" state) conduct.
 *        Programmed cells ("0" state) do not conduct.
 *
 * Vpass: high voltage — any cell (erased or programmed) conducts.
 *        Used to "pass through" regardless of stored weight.
 */
typedef enum {
    SS_V_READ = 0,    /**< Vread: distinguishes erased vs programmed */
    SS_V_PASS = 1     /**< Vpass: always conducts */
} ss_voltage_t;

/**
 * Voltage pattern applied to a word-line pair (WL1, WL2)
 * for one unit synapse.
 */
typedef struct {
    ss_voltage_t v1;   /**< Voltage on WL1 (connected to FG1) */
    ss_voltage_t v2;   /**< Voltage on WL2 (connected to FG2) */
} ss_voltage_pattern_t;

/**
 * @brief Encode a ternary input as a word-line voltage pattern.
 *
 * Patent voltage encoding (Table from FIGS 12-15):
 *   Input -1: V1=Vpass, V2=Vread
 *   Input +1: V1=Vread, V2=Vpass
 *   Input  0: V1=Vread, V2=Vread
 *
 * @param input  Ternary input value (-1, 0, or +1).
 * @return       Voltage pattern for the word-line pair.
 */
static inline ss_voltage_pattern_t ss_encode_input(ss_input_t input)
{
    ss_voltage_pattern_t vp;
    switch (input) {
    case SS_INPUT_NEG:
        vp.v1 = SS_V_PASS;
        vp.v2 = SS_V_READ;
        break;
    case SS_INPUT_POS:
        vp.v1 = SS_V_READ;
        vp.v2 = SS_V_PASS;
        break;
    default: /* 0 */
        vp.v1 = SS_V_READ;
        vp.v2 = SS_V_READ;
        break;
    }
    return vp;
}

/**
 * @brief Detect if a voltage pattern represents a zero input.
 *
 * Zero input is V1=Vread, V2=Vread.  The ZID circuit uses NOR
 * gates on (V1 - Vread) and (V2 - Vread) to detect this.
 *
 * @param vp  Voltage pattern.
 * @return    1 if zero input detected, 0 otherwise.
 */
static inline int ss_is_zero_input(ss_voltage_pattern_t vp)
{
    return (vp.v1 == SS_V_READ) && (vp.v2 == SS_V_READ);
}

/* ===================================================================== */
/* Unit Synapse Model                                                    */
/* ===================================================================== */

/**
 * @brief Memory cell state in a unit synapse.
 *
 * SLC NAND with two threshold states:
 *   ERASED ("1"): low Vth — conducts at Vread
 *   PROGRAMMED ("0"): high Vth — does not conduct at Vread
 *   Both states conduct at Vpass.
 */
typedef enum {
    SS_CELL_ERASED     = 1,   /**< Low Vth: erased "1" state */
    SS_CELL_PROGRAMMED = 0    /**< High Vth: programmed "0" state */
} ss_cell_state_t;

/**
 * @brief Unit synapse: pair of series-connected SLC cells.
 */
typedef struct {
    ss_cell_state_t fg1;   /**< First floating gate cell */
    ss_cell_state_t fg2;   /**< Second floating gate cell, series with fg1 */
} ss_unit_synapse_t;

/**
 * @brief Program a unit synapse with a binary weight.
 *
 * Weight +1: FG1=erased, FG2=programmed
 * Weight -1: FG1=programmed, FG2=erased
 *
 * @param w  Binary weight (+1 or -1).
 * @return   Programmed unit synapse.
 */
static inline ss_unit_synapse_t ss_synapse_program(ss_weight_t w)
{
    ss_unit_synapse_t s;
    if (w == SS_WEIGHT_POS) {
        s.fg1 = SS_CELL_ERASED;
        s.fg2 = SS_CELL_PROGRAMMED;
    } else {
        s.fg1 = SS_CELL_PROGRAMMED;
        s.fg2 = SS_CELL_ERASED;
    }
    return s;
}

/**
 * @brief Read the stored weight from a unit synapse.
 *
 * @param s  Unit synapse to read.
 * @return   Binary weight (+1 or -1).
 */
static inline ss_weight_t ss_synapse_read_weight(ss_unit_synapse_t s)
{
    return (s.fg1 == SS_CELL_ERASED) ? SS_WEIGHT_POS : SS_WEIGHT_NEG;
}

/**
 * @brief Determine if a single cell conducts at a given voltage.
 *
 * At Vread: only erased cells conduct.
 * At Vpass: all cells conduct.
 *
 * @param cell  Cell state (erased or programmed).
 * @param v     Applied voltage (Vread or Vpass).
 * @return      1 if cell conducts, 0 if not.
 */
static inline int ss_cell_conducts(ss_cell_state_t cell, ss_voltage_t v)
{
    if (v == SS_V_PASS)
        return 1;  /* Vpass: always conducts */
    /* Vread: only erased cells conduct */
    return (cell == SS_CELL_ERASED) ? 1 : 0;
}

/**
 * @brief Evaluate a unit synapse: does the NAND string conduct?
 *
 * Both cells in series must conduct for the string to conduct.
 * This performs the in-memory XNOR of input and weight:
 *   - Conducts (+1): input matches weight sign
 *   - Does not conduct (-1): input differs from weight sign
 *   - For zero input: never conducts (-1 for count, but excluded by ZID)
 *
 * @param syn   Unit synapse (stores the weight).
 * @param vp    Voltage pattern (encodes the input).
 * @return      1 if NAND string conducts, 0 if not.
 */
static inline int ss_synapse_eval(ss_unit_synapse_t syn,
                                   ss_voltage_pattern_t vp)
{
    int c1 = ss_cell_conducts(syn.fg1, vp.v1);
    int c2 = ss_cell_conducts(syn.fg2, vp.v2);
    return c1 && c2;  /* Series connection: both must conduct */
}

/* ===================================================================== */
/* Network Mode                                                          */
/* ===================================================================== */

/**
 * @brief Network inference mode.
 */
typedef enum {
    SS_MODE_BNN = 0,   /**< Binary Neural Network: inputs {-1, +1} only */
    SS_MODE_TBN = 1    /**< Ternary-Binary Network: inputs {-1, 0, +1} */
} ss_network_mode_t;

/* ===================================================================== */
/* Parallelism Configuration                                             */
/* ===================================================================== */

/**
 * @brief Parallelism level for inference acceleration.
 */
typedef enum {
    SS_PAR_SEQUENTIAL    = 0,  /**< One synapse per cycle (baseline) */
    SS_PAR_MULTI_BLOCK   = 1,  /**< Multi-block via multi-bit SA */
    SS_PAR_MULTI_PLANE   = 2,  /**< Multi-plane (same weights, diff inputs) */
    SS_PAR_PIPELINED     = 3   /**< Plane pipelining for multi-layer DNN */
} ss_parallelism_t;

/* ===================================================================== */
/* Chip Capabilities                                                     */
/* ===================================================================== */

/**
 * @brief Hardware capability descriptor for Samsung NAND inference chip.
 */
typedef struct {
    uint32_t chip_id;             /**< Silicon revision ID */
    uint32_t patent_class;        /**< G06F7/5443 classification marker */

    /* Network mode support */
    int has_bnn;                  /**< BNN inference support */
    int has_tbn;                  /**< TBN inference support (requires ZID) */
    int has_zid;                  /**< Zero Input Detection circuit */

    /* Memory topology */
    int num_planes;               /**< Number of planes per die */
    int num_blocks_per_plane;     /**< Blocks per plane */
    int num_strings_per_block;    /**< NAND strings (bit lines) per block */
    int num_wl_pairs_per_string;  /**< Word-line pairs (synapses) per string */

    /* Parallelism */
    int sa_bits;                  /**< Sense amplifier width (bits, ≥1) */
    int max_concurrent_blocks;    /**< Max blocks sensed in parallel */
    int supports_plane_pipeline;  /**< Multi-layer pipelining */

    /* Counter/accumulator */
    int counter_bits;             /**< Summation counter width */
    int max_vector_size;          /**< Max input vector dimension S */

    /* Electrical */
    int vread_mv;                 /**< Vread voltage in millivolts */
    int vpass_mv;                 /**< Vpass voltage in millivolts */
} ss_chip_caps_t;

/* ===================================================================== */
/* Platform Mode                                                         */
/* ===================================================================== */

/**
 * @brief Platform execution mode.
 */
typedef enum {
    SS_MODE_EMULATED  = 0,   /**< Software emulation (no real chip) */
    SS_MODE_MMIO      = 1,   /**< Real chip via MMIO registers */
    SS_MODE_SIMULATED = 2    /**< Verilog simulation backend */
} ss_platform_mode_t;

/* ===================================================================== */
/* HAL Runtime State                                                     */
/* ===================================================================== */

/**
 * @brief Runtime state for the Samsung NAND inference HAL.
 */
typedef struct {
    ss_platform_mode_t   mode;        /**< Current execution mode */
    ss_chip_caps_t       caps;        /**< Detected capabilities */
    volatile uint32_t   *mmio_base;   /**< MMIO base (NULL if emulated) */
    ss_network_mode_t    net_mode;    /**< Current network mode (BNN/TBN) */
    ss_parallelism_t     par_level;   /**< Current parallelism level */
    int                  zid_enabled; /**< ZID circuit enabled flag */
    int                  initialized; /**< HAL initialisation flag */
} ss_hal_state_t;

/* ===================================================================== */
/* HAL Lifecycle                                                         */
/* ===================================================================== */

/**
 * @brief Probe for Samsung NAND inference hardware and initialise HAL.
 *
 * On real hardware, reads chip ID from MMIO registers.
 * In emulation mode, populates caps with software-emulated features.
 *
 * @param state  HAL state to initialise.
 * @return       0 on success, -1 on failure.
 */
int ss_hal_init(ss_hal_state_t *state);

/**
 * @brief Shut down the HAL and release MMIO mappings.
 *
 * @param state  HAL state to shut down.
 * @return       0 on success, -1 on failure.
 */
int ss_hal_shutdown(ss_hal_state_t *state);

/**
 * @brief Set the network inference mode (BNN or TBN).
 *
 * When switching to TBN mode, the ZID circuit is automatically enabled
 * via the ZID_Enb mode register bit.
 *
 * @param state  HAL state.
 * @param mode   Network mode to set.
 * @return       0 on success, -1 on failure.
 */
int ss_hal_set_mode(ss_hal_state_t *state, ss_network_mode_t mode);

/**
 * @brief Set the parallelism level for inference.
 *
 * @param state  HAL state.
 * @param level  Parallelism level to configure.
 * @return       0 on success, -1 on failure.
 */
int ss_hal_set_parallelism(ss_hal_state_t *state, ss_parallelism_t level);

/**
 * @brief Query the current platform mode.
 */
static inline ss_platform_mode_t ss_hal_mode(const ss_hal_state_t *state)
{
    return state ? state->mode : SS_MODE_EMULATED;
}

/**
 * @brief Check if the HAL is initialised.
 */
static inline int ss_hal_ready(const ss_hal_state_t *state)
{
    return state && state->initialized;
}

#ifdef __cplusplus
}
#endif

#endif /* SET5_SAMSUNG_US11170290B2_H */
