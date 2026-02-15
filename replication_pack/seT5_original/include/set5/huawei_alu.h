/**
 * @file huawei_alu.h
 * @brief ALU Operations Interface for Huawei CN119652311A Ternary Chip
 *
 * High-level arithmetic operations that map directly to the hardware
 * circuits described in patent CN119652311A:
 *
 *   - Trit-level INC/DEC (single-gate, 1 cycle)
 *   - Ternary sum (Tsum circuit: A + B via NTI/PTI signal routing)
 *   - Half-adder (THA: SUM + CARRY)
 *   - Full-adder (TFA: three-input SUM + CARRY)
 *   - Exact multiply (TMul: 1-trit × 1-trit)
 *   - Approximate multiply (ATMul: ignores carry at input 2×2)
 *   - Wide multiply (2trit×2trit and 6trit×6trit cascaded)
 *   - Compensation units (+6 and +9 for reducing approximation error)
 *
 * All functions accept and return seT5 balanced ternary values
 * {-1, 0, +1}.  The HAL layer performs the translation to the chip's
 * unbalanced {0, 1, 2} encoding internally.
 *
 * When real hardware is not present, all operations fall through to
 * cycle-accurate software emulation of the patent circuits.
 *
 * @see huawei_cn119652311a.h  — Chip header and value translation
 * @see huawei_mmio.h          — MMIO register definitions
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_HUAWEI_ALU_H
#define SET5_HUAWEI_ALU_H

#include "set5/huawei_cn119652311a.h"
#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Approximate Multiplier Compensation Mode                              */
/* ===================================================================== */

/**
 * @brief Compensation mode for approximate multiplication.
 *
 * The patent describes approximate multiplication that ignores the
 * carry when both inputs equal 2 (balanced: +1).  Compensation units
 * can be added to reduce the resulting error:
 *
 *   NONE:   raw approximation (max error, lowest power)
 *   PLUS6:  +6 compensation (P1 bit +2 in ternary), moderate correction
 *   PLUS9:  +9 compensation (P2 bit +1 in ternary), best correction
 */
typedef enum {
    HW_COMP_NONE  = 0,   /**< No compensation */
    HW_COMP_PLUS6 = 1,   /**< +6 compensation (P1 += 2) */
    HW_COMP_PLUS9 = 2    /**< +9 compensation (P2 += 1) */
} hw_compensation_t;

/* ===================================================================== */
/* Single-Trit Gate Operations                                           */
/* ===================================================================== */

/**
 * @brief Self-incrementing gate: (x + 1) mod 3 in Huawei encoding.
 *
 * In balanced ternary terms:
 *   -1 → 0,  0 → +1,  +1 → -1
 *
 * This maps to the patent's 9-transistor INC circuit
 * (7 core + 2 NTI preprocessor).
 *
 * @param state  HAL state (for MMIO dispatch).
 * @param val    Input trit (balanced: -1, 0, +1).
 * @return       Output trit (balanced).
 */
trit hw_alu_inc(const hw_hal_state_t *state, trit val);

/**
 * @brief Self-decrementing gate: (x - 1) mod 3 in Huawei encoding.
 *
 * In balanced ternary:
 *   -1 → +1,  0 → -1,  +1 → 0
 *
 * Maps to the patent's 9-transistor DEC circuit
 * (7 core + 2 PTI preprocessor).
 */
trit hw_alu_dec(const hw_hal_state_t *state, trit val);

/**
 * @brief NTI (Negative Ternary Inverter).
 *
 * Truth table (Huawei): {0→2, 1→0, 2→0}
 * Balanced:             {-1→+1, 0→-1, +1→-1}
 */
trit hw_alu_nti(const hw_hal_state_t *state, trit val);

/**
 * @brief PTI (Positive Ternary Inverter).
 *
 * Truth table (Huawei): {0→2, 1→2, 2→0}
 * Balanced:             {-1→+1, 0→+1, +1→-1}
 */
trit hw_alu_pti(const hw_hal_state_t *state, trit val);

/* ===================================================================== */
/* Ternary Summation (Tsum Circuit)                                      */
/* ===================================================================== */

/**
 * @brief Ternary trit-level sum: (A + B) mod 3, balanced.
 *
 * Implements the patent's summing circuit (Fig. 5):
 *   Signal processing module (NTI₁, PTI, NTI₂, NOR) selects one of
 *   three gating tubes based on input A, routing input B through
 *   INC, DEC, or pass-through accordingly.
 *
 * @param state  HAL state.
 * @param a      First operand trit (balanced).
 * @param b      Second operand trit (balanced).
 * @return       Sum trit (balanced), without carry.
 */
trit hw_alu_tsum(const hw_hal_state_t *state, trit a, trit b);

/* ===================================================================== */
/* Half-Adder (THA Circuit)                                              */
/* ===================================================================== */

/**
 * @brief Ternary half-adder result.
 */
typedef struct {
    trit sum;     /**< Sum trit (balanced) */
    trit carry;   /**< Carry trit (balanced) */
} hw_half_adder_result_t;

/**
 * @brief Ternary half-adder: SUM and CARRY of A + B.
 *
 * Implements patent Fig. 6: the summing circuit produces SUM_AB,
 * and a carry device produces Carry_AB.
 *
 * Carry truth table (balanced ternary addition):
 *   carry = (A + B) / 3  (integer division toward zero, then balanced)
 *
 *      A\\B | -1  |  0  | +1
 *     -----+-----+-----+-----
 *      -1  | -1  |  0  |  0
 *       0  |  0  |  0  |  0
 *      +1  |  0  |  0  | +1
 *
 * @param state  HAL state.
 * @param a      First operand (balanced).
 * @param b      Second operand (balanced).
 * @return       Half-adder result (sum + carry).
 */
hw_half_adder_result_t hw_alu_half_add(const hw_hal_state_t *state,
                                        trit a, trit b);

/* ===================================================================== */
/* Full-Adder (TFA Circuit)                                              */
/* ===================================================================== */

/**
 * @brief Ternary full-adder result.
 */
typedef struct {
    trit sum;     /**< Sum trit (balanced) */
    trit carry;   /**< Carry trit (balanced) */
} hw_full_adder_result_t;

/**
 * @brief Ternary full-adder: SUM and CARRY of A + B + C.
 *
 * Implements patent Fig. 7: two-stage half-adder cascade.
 *   Stage 1: THA(A, B)  → SUM_AB, Carry_AB
 *   Stage 2: THA₂(SUM_AB, C) → SUM_ABC, Carry_SUM
 *   Final carry = carry device(Carry_AB, Carry_SUM)
 *
 * The second stage is optimised per patent Fig. 8: since the
 * carry from stage 1 can only be 0 or ±1, the circuit only needs
 * a +0 (buffer) or +1 (INC) path, eliminating the DEC gate.
 *
 * @param state  HAL state.
 * @param a      First operand (balanced).
 * @param b      Second operand (balanced).
 * @param c      Third operand / carry-in (balanced).
 * @return       Full-adder result (sum + carry).
 */
hw_full_adder_result_t hw_alu_full_add(const hw_hal_state_t *state,
                                        trit a, trit b, trit c);

/* ===================================================================== */
/* Multiplication                                                        */
/* ===================================================================== */

/**
 * @brief Exact 1-trit × 1-trit multiply (TMul).
 *
 * Balanced ternary multiplication truth table:
 *   A\\B | -1  |  0  | +1
 *  -----+-----+-----+-----
 *   -1  | +1  |  0  | -1
 *    0  |  0  |  0  |  0
 *   +1  | -1  |  0  | +1
 *
 * @param state  HAL state.
 * @param a      First trit.
 * @param b      Second trit.
 * @return       Product trit.
 */
trit hw_alu_mul1(const hw_hal_state_t *state, trit a, trit b);

/**
 * @brief Wide multiply result.
 */
typedef struct {
    int  result;          /**< Integer product value */
    int  width_trits;     /**< Trit width of result */
    trit trits[12];       /**< Balanced-trit digits (LST first) */
    int  is_approximate;  /**< 1 if approximate mode was used */
    int  abs_error;       /**< Absolute error vs. exact (0 for exact) */
} hw_mul_result_t;

/**
 * @brief 2-trit × 2-trit multiplication.
 *
 * Implements patent Fig. 11b / Fig. 13:
 *   - 1 exact multiplier   (TMul) for MSB × MSB
 *   - 3 approximate muls   (ATMul) for other partial products
 *   - 1 summing circuit     (Tsum)
 *   - 2 half-adder circuits (THA)
 *
 * @param state  HAL state.
 * @param a      First 2-trit operand as integer (range [-4, +4]).
 * @param b      Second 2-trit operand as integer (range [-4, +4]).
 * @param comp   Compensation mode.
 * @return       Multiplication result.
 */
hw_mul_result_t hw_alu_mul2x2(const hw_hal_state_t *state,
                               int a, int b, hw_compensation_t comp);

/**
 * @brief 6-trit × 6-trit multiplication (cascaded).
 *
 * Implements patent Fig. 14: groups inputs into 2-trit blocks,
 * computes 9 partial products (2trit×2trit each), then sums them
 * with weighted shifts using exact-mode adders.
 *
 * @param state  HAL state.
 * @param a      First 6-trit operand as integer (range [-364, +364]).
 * @param b      Second 6-trit operand as integer (range [-364, +364]).
 * @param comp   Compensation mode.
 * @return       Multiplication result.
 */
hw_mul_result_t hw_alu_mul6x6(const hw_hal_state_t *state,
                               int a, int b, hw_compensation_t comp);

/* ===================================================================== */
/* Multi-Trit Word Arithmetic (using hardware adder chains)              */
/* ===================================================================== */

/**
 * @brief Add two multi-trit words using chained hardware full-adders.
 *
 * Ripple-carry addition of two balanced-ternary words, each stored
 * as an array of trits (LST at index 0).  On real hardware, this
 * chains the full-adder's carry-out → carry-in across trit positions.
 *
 * @param state   HAL state.
 * @param a       First operand trits (length = width).
 * @param b       Second operand trits (length = width).
 * @param result  Output trits (length = width).  May alias a or b.
 * @param width   Number of trits.
 * @return        Final carry trit.
 */
trit hw_alu_add_word(const hw_hal_state_t *state,
                     const trit *a, const trit *b,
                     trit *result, int width);

/**
 * @brief Multiply two multi-trit words.
 *
 * Uses the hardware multiplier in 2-trit blocks when available,
 * falling back to trit-by-trit multiplication otherwise.
 *
 * @param state   HAL state.
 * @param a       First operand as integer.
 * @param b       Second operand as integer.
 * @param comp    Compensation mode for approximate blocks.
 * @return        Multiplication result.
 */
hw_mul_result_t hw_alu_mul_word(const hw_hal_state_t *state,
                                int a, int b, hw_compensation_t comp);

/* ===================================================================== */
/* Multiradix Integration (DOT_TRIT / FFT_STEP acceleration)            */
/* ===================================================================== */

/**
 * @brief Hardware-accelerated ternary dot product.
 *
 * Dispatches to the Huawei chip's chained full-adder array for
 * accumulation when available.  Falls back to multiradix.h dot_trit()
 * in emulation mode.
 *
 * @param state  HAL state.
 * @param a      Array of trits (length = width).
 * @param b      Array of trits (length = width).
 * @param width  Number of elements.
 * @return       Dot product as integer.
 */
int hw_alu_dot_product(const hw_hal_state_t *state,
                       const trit *a, const trit *b, int width);

/**
 * @brief Hardware-accelerated radix-3 FFT butterfly.
 *
 * Uses the chip's summing circuit for the ternary additions in the
 * butterfly:  out[k] = Σ(twiddle[k][j] · in[j]), j=0..2
 *
 * @param state  HAL state.
 * @param in0    First  butterfly input (balanced trit).
 * @param in1    Second butterfly input.
 * @param in2    Third  butterfly input.
 * @param out0   First  butterfly output.
 * @param out1   Second butterfly output.
 * @param out2   Third  butterfly output.
 * @return       0 on success.
 */
int hw_alu_fft_butterfly(const hw_hal_state_t *state,
                         trit in0, trit in1, trit in2,
                         trit *out0, trit *out1, trit *out2);

#ifdef __cplusplus
}
#endif

#endif /* SET5_HUAWEI_ALU_H */
