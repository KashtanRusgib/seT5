/**
 * @file art9_verilog_emu.h
 * @brief C-side emulation wrapper for the ART-9 Verilog pipeline.
 *
 * This header provides a thin C-layer that mirrors the Verilog
 * trit_art9_pipeline module for software-in-the-loop testing.
 * It reuses the existing trit_art9_pipeline.h emulator and adds:
 *
 *   - Verilog-matching 2-bit trit encoding helpers
 *   - Dhrystone-style benchmark program loader
 *   - Pipeline drain / flush verification
 *   - Per-instruction correctness oracle
 *
 * The Verilog file  hw/trit_art9_pipeline.v  is the synthesisable
 * target;  this wrapper validates its functional behaviour in C.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_ART9_VERILOG_EMU_H
#define SET6_ART9_VERILOG_EMU_H

#include "set5/trit_art9_pipeline.h"   /* reuse existing C emulator */
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Verilog trit encoding ============================================ */

/** 2-bit trit encoding matching the Verilog parameters */
#define VEMU_TRIT_NEG   0x0   /* 2'b00 = -1 */
#define VEMU_TRIT_ZERO  0x1   /* 2'b01 =  0 */
#define VEMU_TRIT_POS   0x2   /* 2'b10 = +1 */

/** Convert a balanced integer value to 9-trit 18-bit encoded word */
static inline uint32_t vemu_encode_word(int val) {
    uint32_t word = 0;
    int neg = 0;
    if (val < 0) { neg = 1; val = -val; }
    for (int i = 0; i < ART9_TRITS_PER_WORD; i++) {
        int rem = val % 3;
        val /= 3;
        if (rem == 0)
            word |= ((uint32_t)VEMU_TRIT_ZERO << (2 * i));
        else if (rem == 1) {
            if (neg)
                word |= ((uint32_t)VEMU_TRIT_NEG << (2 * i));
            else
                word |= ((uint32_t)VEMU_TRIT_POS << (2 * i));
        } else { /* rem == 2 → carry */
            if (neg)
                word |= ((uint32_t)VEMU_TRIT_POS << (2 * i));
            else
                word |= ((uint32_t)VEMU_TRIT_NEG << (2 * i));
            val += 1;  /* carry propagation */
        }
    }
    return word;
}

/** Decode an 18-bit trit-encoded word back to balanced integer */
static inline int vemu_decode_word(uint32_t word) {
    int val = 0, pow3 = 1;
    for (int i = 0; i < ART9_TRITS_PER_WORD; i++) {
        int t = (word >> (2 * i)) & 0x3;
        if (t == VEMU_TRIT_POS)      val += pow3;
        else if (t == VEMU_TRIT_NEG) val -= pow3;
        /* VEMU_TRIT_ZERO contributes nothing */
        pow3 *= 3;
    }
    return val;
}

/* ==== Dhrystone-style benchmark program ================================ */

/**
 * @brief Load a Dhrystone-inspired ternary benchmark into an ART-9 state.
 *
 * The benchmark exercises:
 *   - Integer arithmetic (TADD, TSUB, TMUL)
 *   - Logical operations (TAND, TOR, TNOT)
 *   - Shift operations (TSHL, TSHR)
 *   - Memory load/store (TLOAD, TSTORE)
 *   - Branching (TBEQ, TBNE, TBGT, TBLT)
 *   - Loop iteration (emulated via branch-back)
 *   - Compare + branch sequences (pipeline hazard stress)
 *
 * @param st  Initialized ART-9 state.
 * @return Number of instructions loaded, -1 on error.
 */
static inline int vemu_load_dhrystone(art9_state_t *st) {
    if (!st || !st->initialized) return -1;

    /*
     * Dhrystone-like program (ternary):
     *
     *   R0 = loop counter (start = 10)
     *   R1 = accumulator
     *   R2 = temporary
     *   R3 = comparison result
     *   R4 = memory address
     *   R5 = loaded value
     *
     * Section 1: Initialization (instructions 0-4)
     *   TMOVI R0, 10          ; loop count
     *   TMOVI R1, 0           ; accumulator = 0
     *   TMOVI R2, 3           ; step value
     *   TMOVI R4, 0           ; memory base
     *   TMOVI R5, 100         ; store value
     *
     * Section 2: Computation loop (instructions 5-19)
     *   TADD  R1, R1, R2      ; acc += step
     *   TMUL  R2, R2, R2      ; temp = step * step (exercises MUL)
     *   TSHL  R2, R2, _        ; shift left (×3)
     *   TSHR  R2, R2, _        ; shift right (÷3) restores
     *   TAND  R3, R1, R2      ; min(acc, temp)
     *   TOR   R3, R1, R2      ; max(acc, temp)
     *   TNEG  R3, R1, _        ; negate acc
     *   TABS  R3, R3, _        ; absolute value
     *   TSTORE R4, R5, _       ; mem[addr] = val
     *   TADDI R4, R4, 1       ; addr++
     *   TLOAD R5, R4, _        ; val = mem[addr]
     *   TCMP  R3, R1, R0      ; compare acc vs limit
     *   TSUB  R0, R0, _imm:1  ; counter--
     *   TBGT  R0, _, -9       ; if counter > 0, branch back to loop top
     *   NOP                   ; (branch delay filler)
     *
     * Section 3: Finalization (instructions 20-23)
     *   TCLAMP R1, R1, _       ; clamp result
     *   TADDI  R1, R1, 1      ; final adjust
     *   TSUB   R1, R1, R2     ; final subtract
     *   THALT                  ; done
     */
    art9_instruction_t prog[] = {
        /* Section 1: Init */
        { ART9_TMOVI,  0, 0, 0,  10 },   /*  0: R0 = 10          */
        { ART9_TMOVI,  1, 0, 0,   0 },   /*  1: R1 = 0           */
        { ART9_TMOVI,  2, 0, 0,   3 },   /*  2: R2 = 3           */
        { ART9_TMOVI,  4, 0, 0,   0 },   /*  3: R4 = 0           */
        { ART9_TMOVI,  5, 0, 0, 100 },   /*  4: R5 = 100         */

        /* Section 2: Computation loop (starts at PC=5) */
        { ART9_TADD,   1, 1, 2,   0 },   /*  5: R1 = R1 + R2     */
        { ART9_TMUL,   2, 2, 2,   0 },   /*  6: R2 = R2 * R2     */
        { ART9_TSHL,   2, 2, 0,   0 },   /*  7: R2 = R2 << 1 (×3)*/
        { ART9_TSHR,   2, 2, 0,   0 },   /*  8: R2 = R2 >> 1 (÷3)*/
        { ART9_TAND,   3, 1, 2,   0 },   /*  9: R3 = min(R1,R2)  */
        { ART9_TOR,    3, 1, 2,   0 },   /* 10: R3 = max(R1,R2)  */
        { ART9_TNEG,   3, 1, 0,   0 },   /* 11: R3 = -R1         */
        { ART9_TABS,   3, 3, 0,   0 },   /* 12: R3 = |R3|        */
        { ART9_TSTORE, 0, 4, 5,   0 },   /* 13: mem[R4] = R5     */
        { ART9_TADDI,  4, 4, 0,   1 },   /* 14: R4 = R4 + 1      */
        { ART9_TLOAD,  5, 4, 0,   0 },   /* 15: R5 = mem[R4]     */
        { ART9_TCMP,   3, 1, 0,   0 },   /* 16: R3 = cmp(R1,R0)  */
        { ART9_TADDI,  0, 0, 0,  -1 },   /* 17: R0 = R0 - 1      */
        { ART9_TBGT,   0, 0, 0, -13 },   /* 18: if R0>0 goto PC+(-13)=5 */
        { ART9_NOP,    0, 0, 0,   0 },   /* 19: branch delay slot */

        /* Section 3: Finalization */
        { ART9_TCLAMP, 1, 1, 0,   0 },   /* 20: clamp R1         */
        { ART9_TADDI,  1, 1, 0,   1 },   /* 21: R1 += 1          */
        { ART9_TSUB,   1, 1, 2,   0 },   /* 22: R1 -= R2         */
        { ART9_THALT,  0, 0, 0,   0 },   /* 23: halt             */
    };

    int count = (int)(sizeof(prog) / sizeof(prog[0]));
    return art9_load_program(st, prog, count) == 0 ? count : -1;
}

/* ==== Linear-sequence program loader for opcode testing ================ */

/**
 * @brief Load a short sequence of instructions + THALT for testing individual ops.
 *
 * @param st     Initialized ART-9 state.
 * @param insts  Array of instructions.
 * @param count  Number of instructions (THALT appended automatically).
 * @return 0 on success, -1 on error.
 */
static inline int vemu_load_sequence(art9_state_t *st,
                                     const art9_instruction_t *insts,
                                     int count) {
    if (!st || !st->initialized || !insts || count <= 0) return -1;
    if (count + 1 > ART9_MAX_PROGRAM) return -1;

    art9_instruction_t buf[ART9_MAX_PROGRAM];
    for (int i = 0; i < count; i++) buf[i] = insts[i];
    buf[count] = (art9_instruction_t){ ART9_THALT, 0, 0, 0, 0 };

    return art9_load_program(st, buf, count + 1);
}

/* ==== Pipeline statistics helpers ====================================== */

/** Check that CPI is within expected range for a pipelined processor */
static inline int vemu_cpi_in_range(const art9_state_t *st,
                                    int min_cpi_x1000,
                                    int max_cpi_x1000) {
    int cpi = art9_get_cpi(st);
    return (cpi >= min_cpi_x1000 && cpi <= max_cpi_x1000);
}

/** Verify radix economy advantage: ternary should beat binary */
static inline int vemu_radix_economy_beats_binary(int n) {
    int ratio = art9_radix_economy(n);
    return (ratio < 1000);  /* < 1.0 means ternary wins */
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_ART9_VERILOG_EMU_H */
