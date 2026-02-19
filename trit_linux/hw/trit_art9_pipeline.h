/**
 * @file trit_art9_pipeline.h
 * @brief seT6 ART-9 RISC Ternary Pipeline Emulator
 *
 * User-space emulation of a 5-stage ternary RISC pipeline inspired by
 * the ART-9 processor design (arXiv:2111.07584v1). The ART-9 uses 9-trit
 * words (~14-bit binary equivalent) with 24 custom ternary instructions.
 *
 * Key features:
 *   - 5-stage pipeline: Fetch → Decode → Execute → Memory → Writeback
 *   - 24 ternary ALU instructions (TADD, TSUB, TMUL, TNEG, TAND, TOR,
 *     TMIN, TMAX, TSHL, TSHR, TCMP, TLOAD, TSTORE, TNOP, THALT, etc.)
 *   - 9-trit word (balanced ternary: range [-9841, +9841])
 *   - Radix economy metric: density = log₃(n) vs log₂(n)
 *   - Pipeline hazard detection (RAW dependencies)
 *   - Cycle-accurate statistics (DMIPS, CPI, stall count)
 *   - Outlier handling for activation values (LLM inference safe)
 *   - CNTFET energy model (~3.06e6 DMIPS/W theoretical)
 *
 * Reference: "Design and Evaluation of a RISC Ternary Processor"
 *            arXiv:2111.07584v1
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_ART9_PIPELINE_H
#define SET6_TRIT_ART9_PIPELINE_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define ART9_TRITS_PER_WORD    9        /**< 9 trits per ART-9 word       */
#define ART9_WORD_MAX          9841     /**< (3^9 - 1) / 2               */
#define ART9_WORD_MIN         (-9841)   /**< -(3^9 - 1) / 2              */
#define ART9_NUM_REGS          27       /**< 3^3 general registers        */
#define ART9_MEM_SIZE          729      /**< 3^6 memory locations         */
#define ART9_MAX_PROGRAM       256      /**< Max instruction slots        */
#define ART9_PIPELINE_STAGES   5        /**< Fetch/Decode/Exec/Mem/WB     */

/** Energy model constants */
#define ART9_ENERGY_PER_INST_FJ  12     /**< Femtojoules per instruction  */
#define ART9_CNTFET_DMIPS_PW   3060000  /**< CNTFET DMIPS/W theoretical   */
#define ART9_FPGA_DMIPS_PW     58       /**< FPGA emulation DMIPS/W       */
#define ART9_DENSITY_RATIO_PCT 158      /**< 1.58x density vs binary      */

/* ==== Opcodes =========================================================== */

typedef enum {
    ART9_NOP   = 0,     /**< No operation                            */
    ART9_TADD  = 1,     /**< Balanced ternary add: rd = rs1 + rs2    */
    ART9_TSUB  = 2,     /**< Balanced ternary sub: rd = rs1 - rs2    */
    ART9_TMUL  = 3,     /**< Balanced ternary mul: rd = rs1 * rs2    */
    ART9_TNEG  = 4,     /**< Negate: rd = -rs1                       */
    ART9_TAND  = 5,     /**< Kleene AND: rd = min(rs1, rs2)          */
    ART9_TOR   = 6,     /**< Kleene OR: rd = max(rs1, rs2)           */
    ART9_TNOT  = 7,     /**< Kleene NOT: rd = -rs1                   */
    ART9_TMIN  = 8,     /**< Minimum: rd = min(rs1, rs2)             */
    ART9_TMAX  = 9,     /**< Maximum: rd = max(rs1, rs2)             */
    ART9_TSHL  = 10,    /**< Ternary shift left (×3): rd = rs1 * 3   */
    ART9_TSHR  = 11,    /**< Ternary shift right (÷3): rd = rs1 / 3  */
    ART9_TCMP  = 12,    /**< Compare: rd = sign(rs1 - rs2)           */
    ART9_TLOAD = 13,    /**< Load: rd = mem[rs1]                     */
    ART9_TSTORE= 14,    /**< Store: mem[rs1] = rs2                   */
    ART9_TADDI = 15,    /**< Add immediate: rd = rs1 + imm           */
    ART9_TMOVI = 16,    /**< Move immediate: rd = imm                */
    ART9_TBEQ  = 17,    /**< Branch if equal (trit == 0)             */
    ART9_TBNE  = 18,    /**< Branch if not equal (trit != 0)         */
    ART9_TBGT  = 19,    /**< Branch if greater (trit == +1)          */
    ART9_TBLT  = 20,    /**< Branch if less (trit == -1)             */
    ART9_TCLAMP= 21,    /**< Clamp to word range: rd = clamp(rs1)    */
    ART9_TABS  = 22,    /**< Absolute value: rd = |rs1|              */
    ART9_THALT = 23,    /**< Halt execution                          */
    ART9_OP_COUNT = 24  /**< Total instruction count                 */
} art9_opcode_t;

/* ==== Structures ======================================================== */

/**
 * @brief ART-9 instruction word.
 */
typedef struct {
    art9_opcode_t opcode;       /**< Operation code                  */
    int           rd;           /**< Destination register (0..26)    */
    int           rs1;          /**< Source register 1               */
    int           rs2;          /**< Source register 2 / immediate   */
    int           imm;          /**< Immediate value (for TADDI etc) */
} art9_instruction_t;

/**
 * @brief Pipeline stage state (one per stage).
 */
typedef struct {
    int                valid;   /**< Stage contains valid work       */
    art9_instruction_t inst;    /**< Instruction in this stage       */
    int                result;  /**< Computed result (execute stage)  */
    int                stalled; /**< Stage is stalled (hazard)       */
} art9_stage_t;

/**
 * @brief ART-9 processor state.
 */
typedef struct {
    int  initialized;

    /* Registers and memory */
    int  regs[ART9_NUM_REGS];       /**< 27 general registers       */
    int  memory[ART9_MEM_SIZE];     /**< 729-location memory         */

    /* Program */
    art9_instruction_t program[ART9_MAX_PROGRAM];
    int  program_len;                /**< Instructions loaded         */
    int  pc;                         /**< Program counter             */
    int  halted;                     /**< THALT executed              */

    /* Pipeline */
    art9_stage_t stages[ART9_PIPELINE_STAGES];

    /* Statistics */
    int  cycles;                     /**< Total cycles executed       */
    int  instructions_retired;       /**< Instructions completed      */
    int  stalls;                     /**< Pipeline stall cycles       */
    int  branches_taken;             /**< Branch instructions taken   */
    int  outlier_clamps;             /**< Values clamped to range     */
    int64_t energy_fj;               /**< Total energy (femtojoules)  */
} art9_state_t;

/* ==== API =============================================================== */

/**
 * @brief Initialize ART-9 pipeline processor.
 * @param st  State to initialize.
 * @return 0 on success, -1 on NULL.
 */
int art9_init(art9_state_t *st);

/**
 * @brief Load a program into the processor.
 * @param st     Processor state.
 * @param prog   Array of instructions.
 * @param count  Number of instructions.
 * @return 0 on success, -1 on error.
 */
int art9_load_program(art9_state_t *st, const art9_instruction_t *prog,
                      int count);

/**
 * @brief Execute one pipeline cycle.
 *
 * Advances all 5 stages simultaneously, detecting RAW hazards
 * and stalling the pipeline as needed.
 *
 * @param st  Processor state.
 * @return 0 on success, 1 if halted, -1 on error.
 */
int art9_cycle(art9_state_t *st);

/**
 * @brief Run program to completion (until THALT or max cycles).
 * @param st         Processor state.
 * @param max_cycles Maximum cycles before forced halt.
 * @return Number of cycles executed, -1 on error.
 */
int art9_run(art9_state_t *st, int max_cycles);

/**
 * @brief Execute a single ALU instruction (no pipeline).
 *
 * Direct execution for testing individual ops.
 *
 * @param st   Processor state (for register access).
 * @param inst Instruction to execute.
 * @return Result value.
 */
int art9_execute_alu(art9_state_t *st, const art9_instruction_t *inst);

/**
 * @brief Clamp a value to 9-trit balanced ternary range.
 * @param val  Input value.
 * @return Clamped value in [ART9_WORD_MIN, ART9_WORD_MAX].
 */
int art9_clamp(int val);

/**
 * @brief Compute radix economy: log₃(n) / log₂(n).
 *
 * Returns fixed-point ×1000 (e.g., 630 = 0.630 = log₃/log₂ ratio).
 * Ternary is optimal when this is < 1.0 (= 1000 in fixed-point).
 *
 * @param n  Value to evaluate.
 * @return Economy ratio ×1000.
 */
int art9_radix_economy(int n);

/**
 * @brief Get CPI (Cycles Per Instruction) × 1000.
 * @param st  Processor state after execution.
 * @return CPI in fixed-point ×1000.
 */
int art9_get_cpi(const art9_state_t *st);

/**
 * @brief Get estimated DMIPS for current workload.
 * @param st          Processor state after execution.
 * @param freq_mhz    Clock frequency in MHz.
 * @return Estimated DMIPS.
 */
int art9_get_dmips(const art9_state_t *st, int freq_mhz);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_ART9_PIPELINE_H */
