/**
 * @file multiradix.h
 * @brief seT5 Multi-Radix Instructions — DOT_TRIT, FFT_STEP, RADIX_CONV, TRIT_LB
 *
 * Implements the four extended instruction types for multi-radix
 * computation on balanced ternary data:
 *
 *   DOT_TRIT   — Ternary dot product with N:M sparsity (TENET-style)
 *   FFT_STEP   — Radix-3 butterfly for ternary FFT (signal processing)
 *   RADIX_CONV — Balanced ternary ↔ binary conversion
 *   TRIT_LB    — Load-balance telemetry (G300-inspired thermal/utilization)
 *
 * Hardware alignment:
 *   - Huawei CN119652311A: carry-lookahead compatible accumulation
 *   - Samsung CMOS-ternary: 45% area saving on bulk ops
 *   - Memristive 1T1M: 95% power saving on dot product
 *   - FPGA (iCE40/Artix-7): synthesizable from the Verilog ALU
 *
 * @see ARCHITECTURE.md §6 — Multi-Radix Extensions
 * @see trit_emu.h for the underlying SIMD register operations
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_MULTIRADIX_H
#define SET5_MULTIRADIX_H

#include "set5/trit.h"
#include "set5/trit_emu.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Register File ==================================================== */

/** Maximum number of ternary vector registers */
#define MR_NUM_REGS     16
/** Trits per register */
#define MR_REG_WIDTH    32

/**
 * @brief Multi-radix register file.
 *
 * Holds a bank of 32-trit SIMD registers used by the multi-radix
 * instruction unit. Includes telemetry counters for TRIT_LB.
 */
typedef struct {
    trit2_reg32 regs[MR_NUM_REGS];   /**< 16 x 32-trit vector registers */

    /* DOT_TRIT accumulator (ternary arithmetic result) */
    int         dot_acc;             /**< Integer accumulator for dot products */
    int         dot_sparse_skip;     /**< Trits skipped via sparsity */
    int         dot_total_ops;       /**< Total trit multiply-adds */

    /* FFT state */
    int         fft_stage;           /**< Current butterfly stage index */

    /* TRIT_LB telemetry (G300-inspired) */
    int         lb_total_insns;      /**< Total instructions executed */
    int         lb_trit_insns;       /**< Ternary-specific instructions */
    int         lb_sparse_hits;      /**< Times sparsity short-circuit fired */
    int         lb_thermal_limit;    /**< Thermal throttle trigger count */
    int         lb_affinity_migr;    /**< Affinity migration count */
} multiradix_state_t;

/* ==== DOT_TRIT ========================================================= */

/**
 * @brief Ternary dot product of two 32-trit registers.
 *
 * Computes elementwise ternary multiplication (-1,0,+1) and sums
 * the results. Skips zero (Unknown=0) trits for N:M structured
 * sparsity — a register with >50% zeros takes the sparse path.
 *
 * Ternary multiplication truth table:
 *   T * T = T(+1)    T * U = U(0)    T * F = F(-1)
 *   U * x = U(0)     F * F = T(+1)   F * T = F(-1)
 *
 * @param state  Multi-radix state (accumulator + counters updated).
 * @param reg_a  Index of first source register.
 * @param reg_b  Index of second source register.
 * @return       Dot product as balanced integer (range [-32..+32]).
 */
int dot_trit(multiradix_state_t *state, int reg_a, int reg_b);

/**
 * @brief DOT_TRIT with N:M structured sparsity enforcement.
 *
 * Same as dot_trit() but first masks to at most M non-zero positions
 * out of every N-trit block. For 2:4 pattern: keep at most 2 non-zero
 * trits per 4-trit group.
 *
 * @param state  Multi-radix state.
 * @param reg_a  First source register.
 * @param reg_b  Second source register.
 * @param n      Block size (e.g. 4).
 * @param m      Max non-zero per block (e.g. 2).
 * @return       Sparse dot product.
 */
int dot_trit_sparse(multiradix_state_t *state, int reg_a, int reg_b,
                    int n, int m);

/* ==== FFT_STEP ========================================================= */

/**
 * @brief Radix-3 butterfly for ternary FFT.
 *
 * Performs one stage of a ternary FFT butterfly. For a radix-3 transform,
 * three input trits are combined using the ternary rotation:
 *
 *   out[0] = a + b + c        (mod 3, balanced)
 *   out[1] = a + ω·b + ω²·c  (ternary twiddle factor ω = rotation by 1)
 *   out[2] = a + ω²·b + ω·c
 *
 * In balanced ternary, rotation by ω is a cyclic shift: F→U→T→F.
 *
 * @param state   Multi-radix state (fft_stage updated).
 * @param reg_in  Index of input register (trits read in groups of 3).
 * @param reg_out Index of output register.
 * @param stride  Butterfly stride (1, 3, 9, ... for each stage).
 * @return        0 on success, -1 if registers invalid.
 */
int fft_step(multiradix_state_t *state, int reg_in, int reg_out, int stride);

/* ==== RADIX_CONV ======================================================= */

/**
 * @brief Convert a binary integer to balanced ternary in a register.
 *
 * Fills the target register with the balanced ternary representation
 * of the given binary integer. LST (least significant trit) at position 0.
 *
 * Algorithm: repeated division with offset (Avizienis signed-digit).
 *   while n != 0:
 *     r = n % 3
 *     if r == 2: trit = -1, n = (n + 1) / 3
 *     elif r == 1: trit = +1, n = (n - 1) / 3
 *     else: trit = 0, n = n / 3
 *
 * @param state  Multi-radix state.
 * @param reg    Target register index.
 * @param value  Binary integer to convert.
 * @return       Number of non-zero trits written.
 */
int radix_conv_to_ternary(multiradix_state_t *state, int reg, int value);

/**
 * @brief Convert balanced ternary register contents to binary integer.
 *
 * Reconstructs the binary integer from the first `width` trits in
 * the register (position 0 = LST, weight 3^0).
 *
 * @param state  Multi-radix state.
 * @param reg    Source register index.
 * @param width  Number of trits to read (max 20 for 32-bit safe).
 * @return       Binary integer.
 */
int radix_conv_to_binary(const multiradix_state_t *state, int reg, int width);

/* ==== TRIT_LB (Load Balance Telemetry) ================================= */

/**
 * @brief Snapshot of load-balance telemetry.
 *
 * Returned by trit_lb_snapshot(). Models a ternary-aware version of
 * the Google G300 inference accelerator's telemetry system.
 */
typedef struct {
    int total_insns;       /**< Total instructions since last reset */
    int trit_ratio_pct;    /**< Ternary instruction ratio (0-100%) */
    int sparse_ratio_pct;  /**< Sparsity hit ratio (0-100%) */
    int thermal_events;    /**< Number of thermal throttle events */
    int suggested_affinity;/**< Recommended core affinity (-1=any) */
} trit_lb_snapshot_t;

/**
 * @brief Record a multi-radix instruction execution for telemetry.
 * @param state  Multi-radix state.
 */
void trit_lb_record(multiradix_state_t *state);

/**
 * @brief Record a sparsity short-circuit for telemetry.
 * @param state  Multi-radix state.
 */
void trit_lb_sparse_hit(multiradix_state_t *state);

/**
 * @brief Take a telemetry snapshot.
 *
 * Returns a struct with the current instruction mix, sparsity utilization,
 * and thermal event counts. The suggested_affinity field performs a simple
 * heuristic: if trit_ratio > 70%, recommend trit-optimized core (-1 for
 * no recommendation, 0 for binary core, 1 for trit core).
 *
 * @param state  Multi-radix state.
 * @return       Telemetry snapshot.
 */
trit_lb_snapshot_t trit_lb_snapshot(const multiradix_state_t *state);

/**
 * @brief Reset all telemetry counters.
 * @param state  Multi-radix state.
 */
void trit_lb_reset(multiradix_state_t *state);

/**
 * @brief Initialise the multi-radix state.
 *
 * Clears all registers to Unknown, zeroes accumulators and counters.
 *
 * @param state  Multi-radix state to initialise.
 */
void multiradix_init(multiradix_state_t *state);

#ifdef __cplusplus
}
#endif

#endif /* SET5_MULTIRADIX_H */
