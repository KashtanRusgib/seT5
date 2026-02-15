/**
 * @file huawei_mmio.h
 * @brief MMIO Register Map for Huawei CN119652311A Ternary Chip
 *
 * Memory-mapped register definitions for direct hardware access to the
 * Huawei ternary computing chip.  Derived from patent CN119652311A's
 * circuit architecture:
 *
 *   - Voltage module control (VDD, VGND configuration)
 *   - Gate control registers (INC/DEC select, gating tube control)
 *   - ALU operand/result registers (summing, half-adder, full-adder, multiplier)
 *   - Approximate multiplier configuration (compensation mode select)
 *   - Status and interrupt registers
 *
 * Register layout assumes a 4 KB MMIO aperture at a platform-defined
 * base address.  All registers are 32 bits wide.  For multi-trit
 * operands, each trit occupies 2 bits (matching seT6 trit2 encoding
 * after translation through the HAL).
 *
 * On emulated platforms (no real silicon), these addresses are mapped
 * to a software model in huawei_hal.c.
 *
 * @see huawei_cn119652311a.h — Top-level header and value translation
 * @see huawei_alu.h          — High-level ALU operation interface
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_HUAWEI_MMIO_H
#define SET6_HUAWEI_MMIO_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Base Address                                                          */
/* ===================================================================== */

/**
 * Default MMIO base address for the Huawei ternary chip.
 * On real hardware this comes from the device tree / ACPI table.
 * For emulation, a fixed address within the seT6 virtual address space.
 */
#ifndef HW_MMIO_BASE
#define HW_MMIO_BASE            0x40100000UL
#endif

/** MMIO aperture size (4 KB) */
#define HW_MMIO_SIZE            0x1000

/* ===================================================================== */
/* Chip Identification (offset 0x000–0x00F)                              */
/* ===================================================================== */

/** Chip ID register — reads silicon revision */
#define HW_REG_CHIP_ID          0x000
/** Expected chip ID value for CN119652311A */
#define HW_CHIP_ID_EXPECTED     0x48575433   /* "HWT3" in ASCII */

/** Feature register — bit flags for available circuits */
#define HW_REG_FEATURES         0x004

/* Feature register bit definitions */
#define HW_FEAT_INC_GATE        (1u << 0)  /**< Self-incrementing gate */
#define HW_FEAT_DEC_GATE        (1u << 1)  /**< Self-decrementing gate */
#define HW_FEAT_NTI             (1u << 2)  /**< Negative ternary inverter */
#define HW_FEAT_PTI             (1u << 3)  /**< Positive ternary inverter */
#define HW_FEAT_SUMMER          (1u << 4)  /**< Summing circuit (Tsum) */
#define HW_FEAT_HALF_ADDER      (1u << 5)  /**< Half-adder (THA) */
#define HW_FEAT_FULL_ADDER      (1u << 6)  /**< Full-adder (TFA) */
#define HW_FEAT_MULTIPLIER      (1u << 7)  /**< Exact multiplier (TMul) */
#define HW_FEAT_APPROX_MUL      (1u << 8)  /**< Approximate multiplier */
#define HW_FEAT_COMP_PLUS6      (1u << 9)  /**< +6 compensation unit */
#define HW_FEAT_COMP_PLUS9      (1u << 10) /**< +9 compensation unit */
#define HW_FEAT_WIDE_MUL        (1u << 11) /**< 6trit×6trit cascaded mul */

/** All features present on a full-featured chip */
#define HW_FEAT_ALL             0x00000FFF

/** Revision register */
#define HW_REG_REVISION         0x008

/* ===================================================================== */
/* Voltage Module Configuration (offset 0x010–0x01F)                     */
/* ===================================================================== */

/**
 * VDD control register.
 * Bits [15:0] = VDD in millivolts (900–1800).
 * The patent specifies VDD = 0.9V–1.8V, with three logic levels:
 *   VGND = 0V → logic 0
 *   VDD/2     → logic 1
 *   VDD       → logic 2
 */
#define HW_REG_VDD_CTRL         0x010

/**
 * Threshold voltage configuration.
 * Bits [ 7:0]  = LVT threshold (mV / 10), e.g. 25 = 0.25V
 * Bits [15:8]  = MVT threshold (mV / 10), e.g. 40 = 0.40V
 * Bits [23:16] = HVT threshold (mV / 10), e.g. 65 = 0.65V
 * Constraint: LVT + HVT < VDD
 */
#define HW_REG_VTH_CTRL         0x014

/* Threshold extraction macros */
#define HW_VTH_LVT(reg)        (((reg) >>  0) & 0xFF)
#define HW_VTH_MVT(reg)        (((reg) >>  8) & 0xFF)
#define HW_VTH_HVT(reg)        (((reg) >> 16) & 0xFF)
#define HW_VTH_PACK(lvt, mvt, hvt) \
    (((uint32_t)(lvt) & 0xFF) | (((uint32_t)(mvt) & 0xFF) << 8) | \
     (((uint32_t)(hvt) & 0xFF) << 16))

/* ===================================================================== */
/* Gate Control (offset 0x020–0x03F)                                     */
/* ===================================================================== */

/**
 * Gate operation register.
 * Write an operand here with an opcode to trigger a gate operation.
 *
 * Bits [1:0] = input trit value (Huawei encoding: 0, 1, or 2)
 * Bits [7:4] = opcode:
 *   0x0 = INC (self-increment)
 *   0x1 = DEC (self-decrement)
 *   0x2 = NTI
 *   0x3 = PTI
 *   0x4 = PB  (positive buffer)
 *   0x5 = NB  (negative buffer)
 *
 * After write, read HW_REG_GATE_RESULT for the output.
 */
#define HW_REG_GATE_OP          0x020

/* Gate opcodes */
#define HW_GATE_OP_INC          0x00
#define HW_GATE_OP_DEC          0x10
#define HW_GATE_OP_NTI          0x20
#define HW_GATE_OP_PTI          0x30
#define HW_GATE_OP_PB           0x40
#define HW_GATE_OP_NB           0x50

/** Gate result register — bits [1:0] = output trit */
#define HW_REG_GATE_RESULT      0x024

/**
 * Gating tube control.
 * Used by the summing circuit's signal processing module.
 * Bits [1:0] = which tube to conduct (0=first, 1=second, 2=third)
 * Bit  [7]   = auto-select from signal processing module
 */
#define HW_REG_GATING_CTRL      0x028

/* ===================================================================== */
/* ALU Operand Registers (offset 0x040–0x07F)                            */
/* ===================================================================== */

/**
 * Operand A register (multi-trit).
 * Each trit occupies 2 bits, LST at bit 0.  Max 16 trits per register.
 * For a 2trit operand: bits [3:0].
 * For a 6trit operand: bits [11:0].
 */
#define HW_REG_OPERAND_A        0x040

/** Operand B register (same format as A) */
#define HW_REG_OPERAND_B        0x044

/** Operand C register (third input for full-adder) */
#define HW_REG_OPERAND_C        0x048

/** Carry-in register (for chained operations) */
#define HW_REG_CARRY_IN         0x04C

/* ===================================================================== */
/* ALU Operation and Result (offset 0x080–0x0BF)                         */
/* ===================================================================== */

/**
 * ALU command register.
 * Write to trigger an arithmetic operation.
 *
 * Bits [3:0] = operation code:
 *   0x0 = NOP
 *   0x1 = TSUM    (ternary sum: A + B)
 *   0x2 = THA     (half-adder: SUM + CARRY of A + B)
 *   0x3 = TFA     (full-adder: SUM + CARRY of A + B + C)
 *   0x4 = TMUL    (exact multiply: A × B, 1-trit)
 *   0x5 = ATMUL   (approximate multiply: A × B, ignore carry at 2×2)
 *   0x6 = WMUL2   (wide multiply: 2trit × 2trit)
 *   0x7 = WMUL6   (wide multiply: 6trit × 6trit)
 *   0x8 = COMP6   (apply +6 compensation)
 *   0x9 = COMP9   (apply +9 compensation)
 *
 * Bits [7:4] = operand width in trits (1–16)
 * Bit  [8]   = use approximate mode (1 = ATMul instead of TMul)
 * Bit  [9]   = chain carry from HW_REG_CARRY_IN
 */
#define HW_REG_ALU_CMD          0x080

/* ALU operation codes */
#define HW_ALU_NOP              0x0
#define HW_ALU_TSUM             0x1
#define HW_ALU_THA              0x2
#define HW_ALU_TFA              0x3
#define HW_ALU_TMUL             0x4
#define HW_ALU_ATMUL            0x5
#define HW_ALU_WMUL2            0x6
#define HW_ALU_WMUL6            0x7
#define HW_ALU_COMP6            0x8
#define HW_ALU_COMP9            0x9

/* ALU command field helpers */
#define HW_ALU_CMD_BUILD(op, width, approx, chain) \
    ((uint32_t)(op) | (((uint32_t)(width) & 0xF) << 4) | \
     (((uint32_t)!!(approx)) << 8) | (((uint32_t)!!(chain)) << 9))

/** ALU status register — bit 0 = busy, bit 1 = result valid */
#define HW_REG_ALU_STATUS       0x084
#define HW_ALU_STATUS_BUSY      (1u << 0)
#define HW_ALU_STATUS_VALID     (1u << 1)
#define HW_ALU_STATUS_OVERFLOW  (1u << 2)

/** ALU sum/product result register (multi-trit, same encoding as operands) */
#define HW_REG_ALU_RESULT       0x088

/** ALU carry-out register */
#define HW_REG_ALU_CARRY_OUT    0x08C

/**
 * Wide multiply result registers (4 trits per partial product).
 * For 2trit×2trit: P0 (bits [1:0]), P1, P2, P3 in successive words.
 * For 6trit×6trit: P0–P11 in the 12-word result block.
 */
#define HW_REG_MUL_RESULT_BASE  0x090
#define HW_REG_MUL_RESULT(n)    (HW_REG_MUL_RESULT_BASE + 4 * (n))
#define HW_MUL_RESULT_WORDS     12  /**< Max partial product words */

/* ===================================================================== */
/* Approximate Multiplier Config (offset 0x0C0–0x0CF)                    */
/* ===================================================================== */

/**
 * Approximate multiplier configuration.
 * Bits [1:0] = compensation mode:
 *   0 = none (raw approximation)
 *   1 = +6 compensation (P1 bit +2)
 *   2 = +9 compensation (P2 bit +1)
 *   3 = reserved
 */
#define HW_REG_APPROX_CFG       0x0C0

#define HW_APPROX_COMP_NONE     0
#define HW_APPROX_COMP_PLUS6    1
#define HW_APPROX_COMP_PLUS9    2

/** Approximate multiplier error register (last absolute/relative error) */
#define HW_REG_APPROX_ERROR     0x0C4

/* ===================================================================== */
/* Transistor Diagnostic Registers (offset 0x100–0x11F)                  */
/* ===================================================================== */

/**
 * Transistor state register (read-only, diagnostic).
 * Returns the ON/OFF state of the 7 main transistors for the last
 * gate operation, as described in patent Tables 1 and 2.
 *
 * Bit 0 = L1, Bit 1 = L2, Bit 2 = L3
 * Bit 3 = H1, Bit 4 = H2
 * Bit 5 = M1, Bit 6 = M2
 * (1 = ON, 0 = OFF)
 */
#define HW_REG_TRANSISTOR_STATE 0x100

/**
 * Power telemetry register.
 * Bits [15:0] = total transistor switchings since last reset
 * Bits [31:16] = estimated dynamic power (µW, scaled)
 */
#define HW_REG_POWER_TELEM      0x104

/** Operation counter (total ALU ops since reset) */
#define HW_REG_OP_COUNTER       0x108

/** Reset counters (write 1 to clear) */
#define HW_REG_COUNTER_RESET    0x10C

/* ===================================================================== */
/* Interrupt and Error (offset 0x200–0x20F)                              */
/* ===================================================================== */

/** Interrupt status register */
#define HW_REG_INT_STATUS       0x200
#define HW_INT_ALU_DONE         (1u << 0)  /**< ALU operation complete */
#define HW_INT_OVERFLOW         (1u << 1)  /**< Arithmetic overflow */
#define HW_INT_FAULT            (1u << 2)  /**< Fault trit detected */

/** Interrupt enable register */
#define HW_REG_INT_ENABLE       0x204

/** Interrupt clear register (write 1 to clear corresponding bit) */
#define HW_REG_INT_CLEAR        0x208

/* ===================================================================== */
/* MMIO Access Helpers                                                   */
/* ===================================================================== */

/**
 * @brief Read a 32-bit MMIO register.
 * @param base  MMIO base address pointer.
 * @param off   Register offset (from HW_REG_* defines).
 * @return      Register value.
 */
static inline uint32_t hw_mmio_read(volatile uint32_t *base, uint32_t off) {
    return *(volatile uint32_t *)((uint8_t *)base + off);
}

/**
 * @brief Write a 32-bit MMIO register.
 * @param base  MMIO base address pointer.
 * @param off   Register offset (from HW_REG_* defines).
 * @param val   Value to write.
 */
static inline void hw_mmio_write(volatile uint32_t *base, uint32_t off,
                                  uint32_t val) {
    *(volatile uint32_t *)((uint8_t *)base + off) = val;
}

/**
 * @brief Poll until ALU status shows operation complete.
 * @param base     MMIO base address pointer.
 * @param timeout  Maximum polls before giving up.
 * @return         0 if result valid, -1 on timeout.
 */
static inline int hw_mmio_wait_alu(volatile uint32_t *base, int timeout) {
    for (int i = 0; i < timeout; i++) {
        uint32_t st = hw_mmio_read(base, HW_REG_ALU_STATUS);
        if (st & HW_ALU_STATUS_VALID)
            return 0;
    }
    return -1;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_HUAWEI_MMIO_H */
