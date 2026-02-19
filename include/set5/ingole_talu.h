/**
 * @file ingole_talu.h
 * @brief seT5 Hardware Abstraction for WO2016199157A1 Ternary ALU (TALU)
 *
 * Top-level header for the Ternary ALU described in patent WO2016199157A1
 * by Vijay T. Ingole et al.
 *
 * Key patent architecture:
 *
 *   1. Logic values: unbalanced {0, 1, 2} mapped to GND/VDD_2/VDD
 *
 *   2. Unary gates (4 TG each):
 *      - TNOT: zero-sequence complement  {2, 1, 0}
 *      - CWC:  clockwise rotation         {0, 2, 1}
 *      - CCWC: counter-clockwise rotation {1, 0, 2}
 *      - ADD1CARRY: increment with carry
 *
 *   3. Binary gates:
 *      - TAND (min), TNAND, TOR (max), TNOR    — 8 TG each
 *      - XTOR (modular sum)                     — 14 TG
 *      - COMPARATOR (3-state)                   — 10 TG
 *
 *   4. Arithmetic circuits:
 *      - S1: half-adder sum (16 TG)
 *      - S2: full-adder sum (6 TG)
 *      - C2: full carry generator (6 TG)
 *
 *   5. Control:
 *      - 2×9 decoder: 2-trit OPCODE → 9 operations (48 TG)
 *      - Even parity generator (16 TG per stage)
 *
 *   6. Flags: ALL_ZERO, OVERFLOW, EVEN_PARITY_A, EVEN_PARITY_B
 *
 * Mapping to seT5:
 *   seT5 uses balanced {-1, 0, +1}. Ingole uses unbalanced {0, 1, 2}.
 *   Translation: ingole = seT5 + 1,  seT5 = ingole - 1
 *
 * @see docs/INGOLE_WO2016199157A1_INTEGRATION.md — Integration guide
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_INGOLE_TALU_H
#define SET5_INGOLE_TALU_H

#include "set5/trit.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Patent Reference                                                      */
/* ===================================================================== */

#define IG_PATENT_ID         "WO2016199157A1"
#define IG_PATENT_ASSIGNEE   "Individual (Vijay T. Ingole)"
#define IG_PATENT_FILED      "2015-08-03"
#define IG_PATENT_PUBLISHED  "2016-12-15"
#define IG_PATENT_APP        "PCT/IN2015/000307"
#define IG_PATENT_CLASS      "G06F7/49"

/* ===================================================================== */
/* Ingole Unbalanced Ternary Logic Values                                */
/* ===================================================================== */

typedef uint8_t ig_trit;

#define IG_TRIT_0  ((ig_trit)0)   /**< Level 0 (GND)   = seT5 FALSE/-1  */
#define IG_TRIT_1  ((ig_trit)1)   /**< Level 1 (VDD/2) = seT5 UNKNOWN/0 */
#define IG_TRIT_2  ((ig_trit)2)   /**< Level 2 (VDD)   = seT5 TRUE/+1   */

/* ---- Balanced ↔ Unbalanced Conversion -------------------------------- */

static inline ig_trit ig_from_balanced(trit v)
{
    return (ig_trit)(v + 1);
}

static inline trit ig_to_balanced(ig_trit v)
{
    return (trit)((int)v - 1);
}

/* ===================================================================== */
/* OPCODE Enumeration (2-trit decoder → 9 operations)                    */
/* ===================================================================== */

typedef enum {
    IG_OP_NOP            = 0,  /**< D0: No operation        (S0=0,S1=0) */
    IG_OP_AI_TOR_TNOR    = 1,  /**< D1: All Incl TOR/TNOR   (S0=0,S1=1) */
    IG_OP_TOR_TNOR       = 2,  /**< D2: TOR / TNOR          (S0=0,S1=2) */
    IG_OP_AI_TAND_TNAND  = 3,  /**< D3: All Incl TAND/TNAND (S0=1,S1=0) */
    IG_OP_TAND_TNAND     = 4,  /**< D4: TAND / TNAND        (S0=1,S1=1) */
    IG_OP_XTOR_COMP      = 5,  /**< D5: XTOR / Comparator   (S0=1,S1=2) */
    IG_OP_SUB_BA         = 6,  /**< D6: B-A + carry          (S0=2,S1=0) */
    IG_OP_SUB_AB         = 7,  /**< D7: A-B + carry          (S0=2,S1=1) */
    IG_OP_ADD            = 8   /**< D8: A+B + carry          (S0=2,S1=2) */
} ig_opcode_t;

/* ===================================================================== */
/* TALU Result                                                           */
/* ===================================================================== */

/**
 * @brief Result from a TALU word operation.
 *
 * Contains both function outputs (f01, f02), flags, and parity.
 * All values are in seT5 balanced encoding.
 */
typedef struct {
    trit  f01[32];      /**< Primary result per trit position */
    trit  f02[32];      /**< Secondary result per trit position */
    int   width;        /**< Active word width (1..32) */
    trit  overflow;     /**< Carry out of MST: 0=no, +1=overflow */
    trit  all_zero;     /**< 0 if all f01 trits are zero (FALSE/-1) */
    trit  parity_a;     /**< Even parity of operand A */
    trit  parity_b;     /**< Even parity of operand B */
} ig_talu_result_t;

/* ===================================================================== */
/* HAL State                                                             */
/* ===================================================================== */

typedef struct {
    uint32_t chip_id;
    int      is_mmio;           /**< 1 = real silicon, 0 = emulated */
    volatile uint32_t *mmio_base;
    int      max_trit_width;
} ig_hal_state_t;

/**
 * @brief Chip capabilities.
 */
typedef struct {
    uint32_t chip_id;
    uint32_t patent_class;

    /* Gate availability */
    uint8_t has_tnot;
    uint8_t has_cwc;
    uint8_t has_ccwc;
    uint8_t has_add1carry;
    uint8_t has_tand;
    uint8_t has_tnand;
    uint8_t has_tor;
    uint8_t has_tnor;
    uint8_t has_xtor;
    uint8_t has_comparator;
    uint8_t has_half_adder;
    uint8_t has_full_adder;
    uint8_t has_decoder;
    uint8_t has_parity;

    /* Arithmetic */
    uint8_t has_add;
    uint8_t has_sub_ab;
    uint8_t has_sub_ba;

    /* All inclusive */
    uint8_t has_ai_tand;
    uint8_t has_ai_tor;

    /* Flags */
    uint8_t has_all_zero;
    uint8_t has_overflow;
    uint8_t has_even_parity;
} ig_chip_caps_t;

#define IG_CHIP_ID_EXPECTED  0x54414C55  /* "TALU" in ASCII */

/* ===================================================================== */
/* Single-Trit Unary Operations                                          */
/* ===================================================================== */

/**
 * @brief TNOT: ternary NOT (zero-sequence complement).
 * Truth table: {-1→+1, 0→0, +1→-1}  (balanced)
 */
trit ig_alu_tnot(trit val);

/**
 * @brief CWC: clockwise complementary.
 * Truth table: {-1→-1, 0→+1, +1→0}  (balanced)
 */
trit ig_alu_cwc(trit val);

/**
 * @brief CCWC: counter-clockwise complementary.
 * Truth table: {-1→0, 0→-1, +1→+1}  (balanced)
 */
trit ig_alu_ccwc(trit val);

/**
 * @brief ADD_1_CARRY: increment with carry.
 * Returns sum and carry via pointers.
 * {-1→(0,C=0), 0→(+1,C=0), +1→(-1,C=+1)}  (balanced)
 */
void ig_alu_add1carry(trit val, trit *sum, trit *carry);

/* ===================================================================== */
/* Two-Trit Binary Operations                                            */
/* ===================================================================== */

/** TAND: min(A, B) in balanced — Kleene strong conjunction */
trit ig_alu_tand(trit a, trit b);

/** TNAND: TNOT(TAND(A, B)) */
trit ig_alu_tnand(trit a, trit b);

/** TOR: max(A, B) in balanced — Kleene strong disjunction */
trit ig_alu_tor(trit a, trit b);

/** TNOR: TNOT(TOR(A, B)) */
trit ig_alu_tnor(trit a, trit b);

/** XTOR: (A + B) mod 3 in unbalanced → mapped to balanced */
trit ig_alu_xtor(trit a, trit b);

/** COMPARATOR: {0=equal, +1=A>B, -1=A<B} in balanced */
trit ig_alu_comparator(trit a, trit b);

/* ===================================================================== */
/* Arithmetic                                                            */
/* ===================================================================== */

/** Half-adder: S1 + carry */
void ig_alu_half_add(trit a, trit b, trit *sum, trit *carry);

/** Full-adder: S2 + C2 */
void ig_alu_full_add(trit a, trit b, trit cin, trit *sum, trit *carry);

/* ===================================================================== */
/* Word-Level TALU Operations                                            */
/* ===================================================================== */

/**
 * @brief Execute a TALU operation on multi-trit words.
 *
 * @param a       Operand A (array of trits, LST first)
 * @param b       Operand B (array of trits, LST first)
 * @param width   Number of trits (1..32)
 * @param opcode  Operation selector (ig_opcode_t)
 * @param result  Output result structure
 */
void ig_talu_exec(const trit *a, const trit *b, int width,
                  ig_opcode_t opcode, ig_talu_result_t *result);

/* ===================================================================== */
/* HAL Lifecycle                                                         */
/* ===================================================================== */

/** Initialize HAL — detects hardware or falls back to emulation */
int  ig_hal_init(ig_hal_state_t *state);

/** Query chip capabilities */
void ig_hal_caps(const ig_hal_state_t *state, ig_chip_caps_t *caps);

/** Shutdown HAL */
void ig_hal_shutdown(ig_hal_state_t *state);

#ifdef __cplusplus
}
#endif

#endif /* SET5_INGOLE_TALU_H */
