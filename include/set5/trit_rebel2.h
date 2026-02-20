/**
 * @file trit_rebel2.h
 * @brief seT6 — REBEL-2 Balanced Ternary ISA Simulator
 *
 * Models the REBEL-2 architecture described in Steven Bos's 2024 PhD
 * thesis, Chapter 4 and Paper F: a RISC-V-inspired balanced ternary CPU
 * with a 32-trit word size, balanced ternary ISA, and mixed-radix EDA
 * workflow (MRCS-synthesised, OpenLane/FPGA verified).
 *
 * REBEL-2 key properties:
 *   • 32-trit balanced ternary words (-1, 0, +1 per trit)
 *   • No 2's complement — balanced ternary handles sign natively
 *   • Single COMPARE gate (MLE/H51) for <, =, > in one trit
 *   • Radix conversion (binary ↔ ternary) via 176T LUT matrix (Paper E)
 *   • Program counter: 4-trit synchronous tri-directional loadable
 *   • Synthesised with MRCS; taped out at Skywater 130nm (TinyTapeout)
 *
 * This header provides:
 *   rebel2_reg_file_t   — 27-register balanced ternary register file
 *   rebel2_execute_instr — single-instruction ISA simulation
 *   rebel2_radix_convert — signed binary ↔ balanced ternary (4-trit)
 *
 * Instruction set (compressed subset for simulation):
 *   RADD  r_dst, r_src1, r_src2   — balanced ternary add
 *   RSUB  r_dst, r_src1, r_src2   — balanced ternary subtract (no inv needed)
 *   RMOV  r_dst, r_src            — register move
 *   RSET  r_dst, imm              — load trit immediate (-1|0|+1 broadcast)
 *   RCMP  r_dst, r_src1, r_src2   — trit-wise MLE comparison
 *   RNOT  r_dst, r_src            — STI (standard ternary invert)
 *   HALT                          — stop execution
 *
 * Radix conversion (Paper E — "High speed bi-directional binary-ternary
 * interface with CNTFETs"):
 *   4-bit  → 4-trit: 176T, 25 GB/s @ 5 GHz, worst-case delay 80 ps
 *   4-trit → 4-bit:  inverse LUT matrix (table 5 in thesis)
 *   Negative numbers in 2's complement map directly to balanced ternary
 *   without additional circuitry.
 *
 * Formal verification reference:
 *   proof/TritMRCS.thy — rebel2_isa_ternary_error_full
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_REBEL2_H
#define SET6_TRIT_REBEL2_H

#include "set5/trit.h"
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

#ifdef __cplusplus
extern "C"
{
#endif

    /* ============================================================
     * Section 1: REBEL-2 word and register file types
     * ============================================================ */

#define REBEL2_WORD_TRITS 32 /* 32-trit balanced ternary word */
#define REBEL2_NUM_REGS 27   /* 27 registers (3^3 — base-27 indexed) */
#define REBEL2_PC_TRITS 4    /* 4-trit program counter (81 addresses) */

    /**
     * @brief A 32-trit balanced ternary word.
     */
    typedef struct
    {
        int8_t t[REBEL2_WORD_TRITS]; /* each entry: -1, 0, or +1 */
    } rebel2_word_t;

    /**
     * @brief REBEL-2 register file and architectural state.
     */
    typedef struct
    {
        rebel2_word_t reg[REBEL2_NUM_REGS]; /* r0 .. r26 */
        int8_t pc[REBEL2_PC_TRITS];         /* program counter (balanced ternary) */
        bool halted;
        uint64_t cycle_count;
    } rebel2_reg_file_t;

    /* ============================================================
     * Section 2: Word operations
     * ============================================================ */

    /**
     * @brief Initialise a 32-trit word to all UNKNOWN (0).
     */
    static inline void rebel2_word_zero(rebel2_word_t *w)
    {
        if (!w)
            return;
        memset(w->t, 0, REBEL2_WORD_TRITS);
    }

    /**
     * @brief Set all trits of a word to a constant (-1, 0, or +1).
     */
    static inline void rebel2_word_set_const(rebel2_word_t *w, int8_t val)
    {
        if (!w)
            return;
        int8_t v = (val < -1) ? -1 : (val > 1) ? 1
                                               : val;
        for (int i = 0; i < REBEL2_WORD_TRITS; i++)
            w->t[i] = v;
    }

    /**
     * @brief Balanced ternary addition of two 32-trit words with carry.
     *
     * Computes dst = a + b (balanced ternary ripple carry over 32 trits).
     * No 2's complement needed — balanced ternary handles sign natively.
     *
     * @param dst  Result (32 trits, may overflow beyond 32 trits).
     * @param a    First operand.
     * @param b    Second operand.
     */
    static inline void rebel2_word_add(rebel2_word_t *dst,
                                       const rebel2_word_t *a,
                                       const rebel2_word_t *b)
    {
        if (!dst || !a || !b)
            return;
        int8_t carry = 0;
        for (int i = 0; i < REBEL2_WORD_TRITS; i++)
        {
            int sum = a->t[i] + b->t[i] + carry;
            /* Reduce to balanced ternary: range [-1, +1] */
            if (sum > 1)
            {
                dst->t[i] = (int8_t)(sum - 3);
                carry = 1;
            }
            else if (sum < -1)
            {
                dst->t[i] = (int8_t)(sum + 3);
                carry = -1;
            }
            else
            {
                dst->t[i] = (int8_t)sum;
                carry = 0;
            }
        }
        /* Overflow is dropped (32-trit wrapping — consistent with ISA spec) */
    }

    /**
     * @brief Balanced ternary subtraction: dst = a - b.
     *
     * In balanced ternary subtraction = addition of the negation.
     * Negation is trit-wise STI (multiply by -1).
     */
    static inline void rebel2_word_sub(rebel2_word_t *dst,
                                       const rebel2_word_t *a,
                                       const rebel2_word_t *b)
    {
        if (!dst || !a || !b)
            return;
        rebel2_word_t neg_b;
        for (int i = 0; i < REBEL2_WORD_TRITS; i++)
            neg_b.t[i] = (int8_t)(-(b->t[i])); /* STI negation */
        rebel2_word_add(dst, a, &neg_b);
    }

    /**
     * @brief Compute trit-wise MLE (More-Less-Equal) comparison for each position.
     *
     * dst[i] = +1 if a[i] > b[i], -1 if a[i] < b[i], 0 if a[i] == b[i].
     * Single ternary gate per trit (H51 / MLE — Gundersen 2006).
     */
    static inline void rebel2_word_cmp(rebel2_word_t *dst,
                                       const rebel2_word_t *a,
                                       const rebel2_word_t *b)
    {
        if (!dst || !a || !b)
            return;
        for (int i = 0; i < REBEL2_WORD_TRITS; i++)
        {
            if (a->t[i] > b->t[i])
                dst->t[i] = 1;
            else if (a->t[i] < b->t[i])
                dst->t[i] = -1;
            else
                dst->t[i] = 0;
        }
    }

    /**
     * @brief Trit-wise STI (Standard Ternary Inverter) — logical NOT.
     *
     * dst[i] = -a[i]:  +1→-1, 0→0, -1→+1.
     */
    static inline void rebel2_word_not(rebel2_word_t *dst, const rebel2_word_t *a)
    {
        if (!dst || !a)
            return;
        for (int i = 0; i < REBEL2_WORD_TRITS; i++)
            dst->t[i] = (int8_t)(-(a->t[i]));
    }

    /* ============================================================
     * Section 3: ISA instruction set
     * ============================================================ */

    typedef enum
    {
        REBEL2_RADD = 0, /* r_dst = r_src1 + r_src2 */
        REBEL2_RSUB,     /* r_dst = r_src1 - r_src2 */
        REBEL2_RMOV,     /* r_dst = r_src1 */
        REBEL2_RSET,     /* r_dst = broadcast(imm) */
        REBEL2_RCMP,     /* r_dst = MLE(r_src1, r_src2) */
        REBEL2_RNOT,     /* r_dst = STI(r_src1) */
        REBEL2_HALT      /* stop */
    } rebel2_opcode_t;

    /** @brief A single REBEL-2 instruction. */
    typedef struct
    {
        rebel2_opcode_t op;
        uint8_t r_dst;  /* destination register index 0..26 */
        uint8_t r_src1; /* source register 1 index 0..26 */
        uint8_t r_src2; /* source register 2 (if applicable) */
        int8_t imm;     /* immediate trit value (-1, 0, +1) */
    } rebel2_instr_t;

    /**
     * @brief Execute one REBEL-2 instruction.
     *
     * @param rf     Register file / CPU state.
     * @param instr  Instruction to execute.
     */
    static inline void rebel2_execute_instr(rebel2_reg_file_t *rf,
                                            const rebel2_instr_t *instr)
    {
        if (!rf || !instr || rf->halted)
            return;
        if (instr->r_dst >= REBEL2_NUM_REGS)
            return;
        if (instr->r_src1 >= REBEL2_NUM_REGS)
            return;
        if (instr->r_src2 >= REBEL2_NUM_REGS)
            return;

        rebel2_word_t *dst = &rf->reg[instr->r_dst];
        const rebel2_word_t *s1 = &rf->reg[instr->r_src1];
        const rebel2_word_t *s2 = &rf->reg[instr->r_src2];

        switch (instr->op)
        {
        case REBEL2_RADD:
            rebel2_word_add(dst, s1, s2);
            break;
        case REBEL2_RSUB:
            rebel2_word_sub(dst, s1, s2);
            break;
        case REBEL2_RMOV:
            *dst = *s1;
            break;
        case REBEL2_RSET:
            rebel2_word_set_const(dst, instr->imm);
            break;
        case REBEL2_RCMP:
            rebel2_word_cmp(dst, s1, s2);
            break;
        case REBEL2_RNOT:
            rebel2_word_not(dst, s1);
            break;
        case REBEL2_HALT:
            rf->halted = true;
            break;
        }
        rf->cycle_count++;
    }

    /**
     * @brief Initialise register file to all-zero (UNKNOWN) state.
     */
    static inline void rebel2_init(rebel2_reg_file_t *rf)
    {
        if (!rf)
            return;
        for (int r = 0; r < REBEL2_NUM_REGS; r++)
            rebel2_word_zero(&rf->reg[r]);
        memset(rf->pc, 0, sizeof(rf->pc));
        rf->halted = false;
        rf->cycle_count = 0;
    }

    /* ============================================================
     * Section 4: Radix conversion (Paper E)
     *
     * Parallel arithmetic LUT method for signed binary ↔ balanced ternary.
     * 4-bit unsigned binary → 4-trit balanced ternary (and inverse).
     *
     * Table 4 / Table 5 from the thesis: each row expresses the output
     * at position i in base-3 as a sum of the inputs in base-2 (with carry).
     *
     * 176 CNTFET transistors; 97.8 µW at 5 GHz; 25 GB/s nibble conversion.
     * Worst-case delay: 80 ps (≈ 12.5 GHz capability).
     * ============================================================ */

    /**
     * @brief Convert a 4-bit unsigned binary value to 4 balanced trits.
     *
     * Output encoding: trit[0] is least-significant.
     * Balanced ternary range for 4 trits: -40..+40 (integers of form
     * a·27 + b·9 + c·3 + d where a,b,c,d ∈ {-1,0,+1}).
     *
     * @param binary4  unsigned 4-bit value (0..15).
     * @param trits    Output array of 4 balanced trits.
     */
    static inline void rebel2_radix_bin4_to_bal4(uint8_t binary4,
                                                 int8_t trits[4])
    {
        /* Balanced ternary representation of 0..15 */
        static const int8_t lut[16][4] = {
            /* LST-first: [t0, t1, t2, t3] — matches rebel2_bal4_to_int */
            /* val   t0   t1   t2   t3 */
            /* 0 */ { 0,  0,  0,  0},  /* 0           */
            /* 1 */ { 1,  0,  0,  0},  /* 1           */
            /* 2 */ {-1,  1,  0,  0},  /* -1+3 = 2    */
            /* 3 */ { 0,  1,  0,  0},  /* 3           */
            /* 4 */ { 1,  1,  0,  0},  /* 1+3 = 4     */
            /* 5 */ {-1, -1,  1,  0},  /* -1-3+9 = 5  */
            /* 6 */ { 0, -1,  1,  0},  /* -3+9 = 6    */
            /* 7 */ { 1, -1,  1,  0},  /* 1-3+9 = 7   */
            /* 8 */ {-1,  0,  1,  0},  /* -1+9 = 8    */
            /* 9 */ { 0,  0,  1,  0},  /* 9           */
            /* 10 */ { 1,  0,  1,  0}, /* 1+9 = 10    */
            /* 11 */ {-1,  1,  1,  0}, /* -1+3+9 = 11 */
            /* 12 */ { 0,  1,  1,  0}, /* 3+9 = 12    */
            /* 13 */ { 1,  1,  1,  0}, /* 1+3+9 = 13  */
            /* 14 */ {-1, -1, -1,  1}, /* -1-3-9+27=14 */
            /* 15 */ { 0, -1, -1,  1}  /* -3-9+27=15  */
        };
        binary4 &= 0x0Fu;
        for (int i = 0; i < 4; i++)
            trits[i] = lut[binary4][i];
    }

    /**
     * @brief Convert 4 balanced trits to their signed integer value.
     *
     * @param trits  Array of 4 balanced trits (trit[0] = LST).
     * @return       Signed integer value.
     */
    static inline int rebel2_bal4_to_int(const int8_t trits[4])
    {
        int val = 0, base = 1;
        for (int i = 0; i < 4; i++)
        {
            val += trits[i] * base;
            base *= 3;
        }
        return val;
    }

    /**
     * @brief Convert a 4-bit 2's complement signed value to 4 balanced trits.
     *
     * Negative binary values (2's complement) convert directly to balanced
     * ternary without extra circuitry (Bos Paper E, DISCUSSION section).
     *
     * @param signed4  Signed 4-bit value (-8..+7).
     * @param trits    Output array of 4 balanced trits.
     */
    static inline void rebel2_radix_signed4_to_bal4(int8_t signed4,
                                                    int8_t trits[4])
    {
        int v = (int)signed4;
        for (int i = 0; i < 4; i++)
        {
            int r = v % 3;
            /* Map remainder to balanced {-1,0,+1} */
            if (r > 1)
            {
                r -= 3;
            }
            else if (r < -1)
            {
                r += 3;
            }
            trits[i] = (int8_t)r;
            v = (v - r) / 3;
        }
    }

#ifdef __cplusplus
}
#endif
#endif /* SET6_TRIT_REBEL2_H */
