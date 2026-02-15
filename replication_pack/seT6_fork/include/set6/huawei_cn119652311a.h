/**
 * @file huawei_cn119652311a.h
 * @brief seT6 Hardware Abstraction for Huawei CN119652311A Ternary Chip
 *
 * Top-level header for Huawei's ternary logic gate / computing circuit /
 * chip as described in patent CN119652311A (filed 2023-09-18, published
 * 2025-03-18, assignee Huawei Technologies Co., Ltd.).
 *
 * Key patent architecture:
 *
 *   1. Logic values:  {0, 1, 2}  mapped to voltage levels
 *      VGND → 0,  VDD/2 → 1,  VDD → 2
 *
 *   2. Fundamental gates (7 CNTFET transistors + 2 preprocessor):
 *      - Self-incrementing gate (INC):  out = (in + 1) mod 3
 *      - Self-decrementing gate (DEC):  out = (in - 1) mod 3
 *      These two gates compose ALL 27 single-variable ternary functions.
 *
 *   3. Three transistor threshold classes (CNTFET):
 *      - LVT (Low Vth):    0.20–0.30 V
 *      - MVT (Medium Vth):  0.40 V
 *      - HVT (High Vth):   0.60–0.70 V
 *      Constraint: LVT + HVT < VDD
 *
 *   4. Preprocessors:
 *      - NTI (Negative Ternary Inverter): {0→2, 1→0, 2→0}
 *      - PTI (Positive Ternary Inverter): {0→2, 1→2, 2→0}
 *
 *   5. Computing circuits built from INC/DEC:
 *      - Summing circuit  (Tsum):  A + B  via NTI/PTI signal routing
 *      - Half-adder       (THA):   SUM + CARRY for 2 inputs
 *      - Full-adder       (TFA):   SUM + CARRY for 3 inputs
 *      - Multiplier       (TMul):  exact 1-trit multiply
 *      - Approximate mult (ATMul): ignores carry when A=B=2 (AI workloads)
 *
 *   6. Scalable multiplication: 2trit×2trit → 6trit×6trit and beyond
 *      via partial-product cascading with optional compensation (+6, +9).
 *
 * Mapping to seT6:
 *   seT6 uses balanced ternary {-1, 0, +1} (TRIT_FALSE/UNKNOWN/TRUE).
 *   Huawei uses unbalanced {0, 1, 2}.
 *   Translation:  huawei_val = seT6_val + 1
 *                 seT6_val   = huawei_val - 1
 *
 * This header provides:
 *   - Logic value translation macros
 *   - Chip identification and capability query
 *   - Platform detection (real hardware vs. emulation)
 *   - Combined include for all Huawei sub-headers
 *
 * @see huawei_mmio.h  — Memory-mapped register definitions
 * @see huawei_alu.h   — ALU operation interface
 * @see HUAWEI_2025_TERNARY_CHIP_PATENT_CN119652311A.md — Full patent text
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_HUAWEI_CN119652311A_H
#define SET6_HUAWEI_CN119652311A_H

#include "set6/trit.h"
#include "set6/trit_emu.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Patent Reference                                                      */
/* ===================================================================== */

#define HW_PATENT_ID          "CN119652311A"
#define HW_PATENT_ASSIGNEE    "Huawei Technologies Co., Ltd."
#define HW_PATENT_FILED       "2023-09-18"
#define HW_PATENT_PUBLISHED   "2025-03-18"
#define HW_PATENT_PCT         "PCT/CN2024/119205"
#define HW_PATENT_CLASS       "G06F7/49"  /* Ternary radix computation */

/* ===================================================================== */
/* Huawei Ternary Logic Values                                           */
/* ===================================================================== */

/**
 * Huawei CN119652311A uses unbalanced ternary {0, 1, 2} mapped to
 * voltage levels: VGND → 0,  VDD/2 → 1,  VDD → 2.
 *
 * seT6 uses balanced ternary {-1, 0, +1}.
 * Conversion: hw = balanced + 1,  balanced = hw - 1.
 */

typedef uint8_t hw_trit;   /**< Huawei logic value: 0, 1, or 2 */

#define HW_TRIT_0   ((hw_trit)0)   /**< Huawei logic 0 (= seT6 FALSE/-1)  */
#define HW_TRIT_1   ((hw_trit)1)   /**< Huawei logic 1 (= seT6 UNKNOWN/0) */
#define HW_TRIT_2   ((hw_trit)2)   /**< Huawei logic 2 (= seT6 TRUE/+1)   */

/* ---- Balanced ↔ Unbalanced Conversion -------------------------------- */

/**
 * @brief Convert seT6 balanced trit {-1,0,+1} to Huawei {0,1,2}.
 */
static inline hw_trit hw_from_balanced(trit v) {
    return (hw_trit)(v + 1);
}

/**
 * @brief Convert Huawei {0,1,2} to seT6 balanced trit {-1,0,+1}.
 */
static inline trit hw_to_balanced(hw_trit v) {
    return (trit)(v - 1);
}

/**
 * @brief Convert a seT6 2-bit packed trit to Huawei hw_trit.
 *
 * seT6 trit2 encoding: 00=-1(F), 01=0(U), 11=+1(T), 10=fault
 * Huawei encoding:     0, 1, 2
 */
static inline hw_trit hw_from_trit2(trit2 t) {
    return hw_from_balanced((trit)trit2_decode(t));
}

/**
 * @brief Convert Huawei hw_trit to seT6 2-bit packed trit.
 */
static inline trit2 hw_to_trit2(hw_trit v) {
    return trit2_encode((int)(v - 1));
}

/* ===================================================================== */
/* 27 Single-Variable Functions (f0–f26)                                 */
/* ===================================================================== */

/**
 * The patent enumerates all 3^3 = 27 single-variable functions of
 * three-valued logic, ordered by their ternary digit representation
 * {f(0), f(1), f(2)}.  The INC and DEC gates implement f19 and f7:
 *
 *   f19 = {2, 0, 1}  →  INC:  (x + 1) mod 3
 *   f7  = {0, 2, 1}  →  DEC:  (x - 1) mod 3   [actually f7 = {0,2,1}]
 *
 * Wait — let's verify from the patent:
 *   INC: 0→1, 1→2, 2→0  →  f(0)=1, f(1)=2, f(2)=0  = {1,2,0} = f5
 *   DEC: 0→2, 1→0, 2→1  →  f(0)=2, f(1)=0, f(2)=1  = {2,0,1} = f19
 *
 * These two gates, combined with NTI {2,0,0}=f18 and PTI {2,2,0}=f24,
 * can synthesize all 27 functions.
 */

/** INC gate truth table: {1, 2, 0} — function f5 */
static inline hw_trit hw_gate_inc(hw_trit x) {
    return (hw_trit)((x + 1) % 3);
}

/** DEC gate truth table: {2, 0, 1} — function f19 */
static inline hw_trit hw_gate_dec(hw_trit x) {
    return (hw_trit)((x + 2) % 3);   /* (x - 1) mod 3 = (x + 2) mod 3 */
}

/** NTI (Negative Ternary Inverter): {2, 0, 0} — function f18 */
static inline hw_trit hw_gate_nti(hw_trit x) {
    return (x == HW_TRIT_0) ? HW_TRIT_2 : HW_TRIT_0;
}

/** PTI (Positive Ternary Inverter): {2, 2, 0} — function f24 */
static inline hw_trit hw_gate_pti(hw_trit x) {
    return (x == HW_TRIT_2) ? HW_TRIT_0 : HW_TRIT_2;
}

/** PB (Positive Buffer): {0, 2, 2} — function f8 */
static inline hw_trit hw_gate_pb(hw_trit x) {
    return (x == HW_TRIT_0) ? HW_TRIT_0 : HW_TRIT_2;
}

/** NB (Negative Buffer): {0, 0, 2} — function f2 */
static inline hw_trit hw_gate_nb(hw_trit x) {
    return (x == HW_TRIT_2) ? HW_TRIT_2 : HW_TRIT_0;
}

/* ===================================================================== */
/* Chip Capabilities and Detection                                       */
/* ===================================================================== */

/**
 * @brief Hardware capability flags returned by hw_chip_probe().
 */
typedef struct {
    uint32_t chip_id;          /**< Silicon revision ID */
    uint32_t patent_class;     /**< G06F7/49 ternary radix marker */

    /* Feature flags */
    int has_inc_gate;          /**< Self-incrementing gate present */
    int has_dec_gate;          /**< Self-decrementing gate present */
    int has_half_adder;        /**< Ternary half-adder circuit */
    int has_full_adder;        /**< Ternary full-adder circuit */
    int has_multiplier;        /**< Exact 1-trit multiplier */
    int has_approx_mul;        /**< Approximate multiplier (AI mode) */
    int has_compensation;      /**< +6/+9 compensation units */

    /* Electrical parameters */
    int vdd_mv;                /**< VDD in millivolts (900–1800) */
    int vth_lvt_mv;            /**< LVT threshold (200–300 mV) */
    int vth_mvt_mv;            /**< MVT threshold (~400 mV) */
    int vth_hvt_mv;            /**< HVT threshold (600–700 mV) */

    /* Scale */
    int max_trit_width;        /**< Max multi-trit word width */
    int mul_width;             /**< Native multiplier width (trits) */
    int num_alu_units;         /**< Number of parallel ALU units */
} hw_chip_caps_t;

/**
 * @brief Platform execution mode.
 */
typedef enum {
    HW_MODE_EMULATED  = 0,   /**< Software emulation (no real chip) */
    HW_MODE_MMIO      = 1,   /**< Real chip via MMIO registers */
    HW_MODE_SIMULATED = 2    /**< Verilog simulation backend */
} hw_platform_mode_t;

/**
 * @brief Runtime state for the Huawei HAL.
 */
typedef struct {
    hw_platform_mode_t  mode;      /**< Current execution mode */
    hw_chip_caps_t      caps;      /**< Detected capabilities */
    volatile uint32_t  *mmio_base; /**< MMIO base address (NULL if emulated) */
    int                 initialized;
} hw_hal_state_t;

/* ---- HAL Lifecycle --------------------------------------------------- */

/**
 * @brief Probe for Huawei CN119652311A hardware and initialise the HAL.
 *
 * On real hardware, reads the chip ID from MMIO registers.
 * In emulation mode, populates caps with software-emulated features.
 *
 * @param state  HAL state to initialise.
 * @return       0 on success, -1 on failure.
 */
int hw_hal_init(hw_hal_state_t *state);

/**
 * @brief Shut down the HAL and release MMIO mappings.
 */
int hw_hal_shutdown(hw_hal_state_t *state);

/**
 * @brief Query the current platform mode.
 */
static inline hw_platform_mode_t hw_hal_mode(const hw_hal_state_t *state) {
    return state ? state->mode : HW_MODE_EMULATED;
}

/**
 * @brief Check if a specific capability is available.
 */
static inline int hw_has_feature(const hw_hal_state_t *state, int flag) {
    (void)flag;
    return state && state->initialized;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_HUAWEI_CN119652311A_H */
