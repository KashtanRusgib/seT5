/**
 * @file samsung_nand.h
 * @brief NAND Array Model and MMIO Register Map for Samsung US11170290B2
 *
 * Defines the NAND flash memory topology and memory-mapped register
 * interface for the Samsung in-memory neural network inference chip
 * (US11170290B2).
 *
 * Memory Hierarchy (patent FIGS 1-4):
 *   Controller → Memory Package → Memory Die
 *     Die: Control Circuitry 310 + Memory Structure 326
 *     Memory Structure: Planes → Blocks → NAND Strings
 *     NAND String: series-connected memory cells sharing a bit line
 *     Unit Synapse: pair of adjacent cells on a NAND string
 *
 * Controller Architecture:
 *   Front End Processor (FEP): Host interface, FTL/MML, DRAM management
 *   Back End Processor (BEP): Memory ops, ECC, Toggle Mode interfaces
 *
 * MMIO Register Map:
 *   0x000–0x00F: Chip identification
 *   0x010–0x01F: Mode configuration (BNN/TBN, ZID enable)
 *   0x020–0x03F: Input vector registers
 *   0x040–0x05F: Weight programming registers
 *   0x060–0x07F: Dot-product result and counter registers
 *   0x080–0x09F: Parallelism and plane configuration
 *   0x0A0–0x0BF: ZID circuit control
 *   0x0C0–0x0DF: Status and interrupt registers
 *   0x100–0x1FF: Block/plane selection and multi-block control
 *
 * @see samsung_us11170290b2.h — Top-level header
 * @see samsung_tbn.h          — TBN inference engine interface
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SAMSUNG_NAND_H
#define SET5_SAMSUNG_NAND_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Default Configuration                                                 */
/* ===================================================================== */

/** Default MMIO base address for Samsung NAND inference chip */
#ifndef SS_MMIO_BASE
#define SS_MMIO_BASE              0x40200000UL
#endif

/** MMIO aperture size (4 KB) */
#define SS_MMIO_SIZE              0x1000

/* ===================================================================== */
/* NAND Array Topology Defaults                                          */
/* ===================================================================== */

/** Maximum number of planes per die */
#define SS_MAX_PLANES             4

/** Maximum number of blocks per plane */
#define SS_MAX_BLOCKS_PER_PLANE   64

/** Maximum number of NAND strings (bit lines) per block */
#define SS_MAX_STRINGS_PER_BLOCK  256

/** Maximum unit synapses (word-line pairs) per NAND string */
#define SS_MAX_SYNAPSES_PER_STRING 128

/** Maximum input vector size (total synapses addressable) */
#define SS_MAX_VECTOR_SIZE        (SS_MAX_SYNAPSES_PER_STRING)

/** Maximum weight matrix dimension per plane */
#define SS_MAX_MATRIX_ROWS        SS_MAX_STRINGS_PER_BLOCK
#define SS_MAX_MATRIX_COLS        SS_MAX_SYNAPSES_PER_STRING

/* ===================================================================== */
/* Chip Identification Registers (0x000–0x00F)                           */
/* ===================================================================== */

/** Chip ID register */
#define SS_REG_CHIP_ID            0x000
/** Expected chip ID for US11170290B2 inference engine */
#define SS_CHIP_ID_EXPECTED       0x534E4E49   /* "SNNI" — Samsung NAND Neural Inference */

/** Feature register — bit flags for available circuits */
#define SS_REG_FEATURES           0x004

/* Feature register bit definitions */
#define SS_FEAT_BNN               (1u << 0)  /**< Binary NN inference */
#define SS_FEAT_TBN               (1u << 1)  /**< Ternary-Binary NN inference */
#define SS_FEAT_ZID               (1u << 2)  /**< Zero Input Detection circuit */
#define SS_FEAT_MULTI_BLOCK       (1u << 3)  /**< Multi-block parallelism */
#define SS_FEAT_MULTI_PLANE       (1u << 4)  /**< Multi-plane parallelism */
#define SS_FEAT_PIPELINE          (1u << 5)  /**< Plane pipelining */
#define SS_FEAT_MULTI_BIT_SA      (1u << 6)  /**< Multi-bit sense amplifiers */
#define SS_FEAT_COUNTER_CSC       (1u << 7)  /**< Counter-based summation circuit */

/** All features present on a full-featured chip */
#define SS_FEAT_ALL               0x000000FF

/** Revision register */
#define SS_REG_REVISION           0x008

/** Topology register: encodes planes, blocks, strings, synapses */
#define SS_REG_TOPOLOGY           0x00C

/* Topology register field extraction */
#define SS_TOPO_PLANES(reg)       (((reg) >> 0) & 0xFF)
#define SS_TOPO_BLOCKS(reg)       (((reg) >> 8) & 0xFF)
#define SS_TOPO_STRINGS(reg)      (((reg) >> 16) & 0xFF)
#define SS_TOPO_SYNAPSES(reg)     (((reg) >> 24) & 0xFF)
#define SS_TOPO_PACK(planes, blocks, strings, synapses) \
    (((uint32_t)(planes) & 0xFF) | \
     (((uint32_t)(blocks) & 0xFF) << 8) | \
     (((uint32_t)(strings) & 0xFF) << 16) | \
     (((uint32_t)(synapses) & 0xFF) << 24))

/* ===================================================================== */
/* Mode Configuration Registers (0x010–0x01F)                            */
/* ===================================================================== */

/**
 * Mode register.
 * Bit [0]   = Network mode: 0=BNN, 1=TBN
 * Bit [1]   = ZID_Enb: Zero Input Detection enable
 * Bits [3:2] = Parallelism level: 00=seq, 01=multi-block,
 *              10=multi-plane, 11=pipelined
 * Bits [7:4] = Active blocks for multi-block mode (count - 1)
 * Bits [9:8] = Active planes for multi-plane mode (count - 1)
 */
#define SS_REG_MODE               0x010

#define SS_MODE_BIT_TBN           (1u << 0)
#define SS_MODE_BIT_ZID_ENB       (1u << 1)
#define SS_MODE_PAR_SHIFT         2
#define SS_MODE_PAR_MASK          (0x3u << SS_MODE_PAR_SHIFT)
#define SS_MODE_ACTIVE_BLK_SHIFT  4
#define SS_MODE_ACTIVE_BLK_MASK   (0xFu << SS_MODE_ACTIVE_BLK_SHIFT)
#define SS_MODE_ACTIVE_PL_SHIFT   8
#define SS_MODE_ACTIVE_PL_MASK    (0x3u << SS_MODE_ACTIVE_PL_SHIFT)

/**
 * Vector size register.
 * Bits [15:0] = Input vector dimension S (number of synapses per string).
 * Used by the counter correction logic: P = 2·CNT − (S − Z).
 */
#define SS_REG_VECTOR_SIZE        0x014

/**
 * Layer configuration register.
 * Bits [7:0]  = Current layer index (for pipelining)
 * Bits [15:8] = Total layers in DNN
 */
#define SS_REG_LAYER_CONFIG       0x018

/* ===================================================================== */
/* Input Vector Registers (0x020–0x03F)                                  */
/* ===================================================================== */

/**
 * Input vector registers — packed ternary inputs.
 *
 * Each input occupies 2 bits:
 *   00 = input -1, 01 = input 0, 11 = input +1, 10 = reserved
 *
 * This matches the seT5 trit2 encoding after trit_pack().
 *
 * 8 registers × 32 bits = 128 inputs maximum.
 * Register 0 holds inputs [0..15], Register 1 holds [16..31], etc.
 */
#define SS_REG_INPUT_VEC_BASE     0x020
#define SS_REG_INPUT_VEC(n)       (SS_REG_INPUT_VEC_BASE + ((n) * 4))
#define SS_INPUT_VEC_REGS         8   /**< Number of input vector registers */
#define SS_INPUTS_PER_REG         16  /**< Inputs per 32-bit register */

/* ===================================================================== */
/* Weight Programming Registers (0x040–0x05F)                            */
/* ===================================================================== */

/**
 * Weight programming target register.
 * Bits [7:0]   = Block index
 * Bits [15:8]  = String (bit line) index
 * Bits [23:16] = Synapse (word-line pair) index within string
 * Bit  [24]    = Weight value: 0 = weight -1, 1 = weight +1
 * Bit  [31]    = Write trigger (set to 1, auto-clears)
 */
#define SS_REG_WEIGHT_PROG        0x040

/** Bulk weight programming: row of weights (one per bit line in a block) */
#define SS_REG_WEIGHT_ROW_BASE    0x044
#define SS_REG_WEIGHT_ROW(n)      (SS_REG_WEIGHT_ROW_BASE + ((n) * 4))
#define SS_WEIGHT_ROW_REGS        6   /**< 6 regs × 32 bits = 192 weights */

/**
 * Weight programming status.
 * Bit [0] = Programming complete
 * Bit [1] = Programming error
 */
#define SS_REG_WEIGHT_STATUS      0x05C

/* ===================================================================== */
/* Dot-Product Result / Counter Registers (0x060–0x07F)                  */
/* ===================================================================== */

/**
 * Raw counter output register.
 * Bits [15:0] = CNT_out: count of conducting NAND strings.
 * For multi-bit SA: each bit position from a different block.
 */
#define SS_REG_CNT_OUT            0x060

/**
 * Zero count register (TBN mode only).
 * Bits [15:0] = Z: number of zero inputs detected by ZID circuit.
 */
#define SS_REG_ZERO_COUNT         0x064

/**
 * Dot-product result register (corrected).
 * Bits [15:0] = Signed dot-product P (two's complement).
 *
 * BNN: P = 2·CNT_out − S
 * TBN: P = 2·CNT_out − (S − Z)
 *
 * The correction is applied by hardware when ZID is enabled.
 */
#define SS_REG_DOT_PRODUCT        0x068

/**
 * Effective S register (after zero correction).
 * Bits [15:0] = S_tbn = S − Z (for TBN); equals S for BNN.
 */
#define SS_REG_S_EFFECTIVE        0x06C

/**
 * Multi-output dot-product registers for parallel bit lines.
 * Each register holds the dot-product for one output neuron.
 * SS_REG_DOT_MULTI(0) = same as SS_REG_DOT_PRODUCT for string 0.
 */
#define SS_REG_DOT_MULTI_BASE     0x070
#define SS_REG_DOT_MULTI(n)       (SS_REG_DOT_MULTI_BASE + ((n) * 4))
#define SS_DOT_MULTI_REGS         4    /**< Up to 4 parallel outputs */

/* ===================================================================== */
/* Parallelism / Block-Plane Selection (0x080–0x0BF)                     */
/* ===================================================================== */

/**
 * Block selection register for multi-block sensing.
 * Each bit enables the corresponding block for parallel read.
 * Bit N = 1: Block N participates in multi-block operation.
 */
#define SS_REG_BLOCK_SELECT       0x080

/**
 * Plane selection register for multi-plane operation.
 * Bit N = 1: Plane N active for parallel inference.
 */
#define SS_REG_PLANE_SELECT       0x084

/**
 * Pipeline stage register.
 * Bits [7:0]  = Source plane (output producer)
 * Bits [15:8] = Destination plane (input consumer)
 * Bit  [16]   = Pipeline enable
 */
#define SS_REG_PIPELINE_CTRL      0x088

/**
 * Sense amplifier configuration.
 * Bits [3:0] = SA bit width (1, 2, 4, or 8)
 * Bit  [4]   = Multi-bit SA enable
 */
#define SS_REG_SA_CONFIG          0x08C

/* ===================================================================== */
/* ZID Circuit Control (0x0A0–0x0BF)                                     */
/* ===================================================================== */

/**
 * ZID control register.
 * Bit [0]   = ZID enable (mirrors SS_MODE_BIT_ZID_ENB)
 * Bit [1]   = ZID auto-mode (tied to TBN mode selection)
 * Bits [7:2] = Reserved
 */
#define SS_REG_ZID_CTRL           0x0A0

/**
 * ZID detected zeros bitmap (per word-line pair).
 * 4 registers × 32 bits = 128 synapse positions.
 * Bit N = 1: synapse N received a zero input.
 */
#define SS_REG_ZID_BITMAP_BASE    0x0A4
#define SS_REG_ZID_BITMAP(n)      (SS_REG_ZID_BITMAP_BASE + ((n) * 4))
#define SS_ZID_BITMAP_REGS        4

/**
 * BCC (Block Counter Control) signal register.
 * Bit [0] = BCC signal active: counter should skip current synapse.
 * Read-only; driven by ZID combinational logic output.
 */
#define SS_REG_BCC_SIGNAL         0x0B4

/* ===================================================================== */
/* Status and Control (0x0C0–0x0DF)                                      */
/* ===================================================================== */

/**
 * Command register — triggers inference operations.
 * Bits [3:0] = Command code:
 *   0x0 = NOP
 *   0x1 = COMPUTE_DOT     — single dot-product (one string)
 *   0x2 = COMPUTE_ROW     — dot-product for all strings in a block
 *   0x3 = COMPUTE_BLOCK   — multi-block parallel dot-product
 *   0x4 = COMPUTE_PLANE   — multi-plane parallel inference
 *   0x5 = COMPUTE_PIPE    — pipelined multi-layer inference
 *   0x6 = PROGRAM_WEIGHTS — program weight matrix to NAND cells
 *   0x7 = READ_WEIGHTS    — read back weight matrix
 * Bit [4] = Start (write 1 to trigger, auto-clears)
 */
#define SS_REG_COMMAND            0x0C0

/* Command codes */
#define SS_CMD_NOP                0x00
#define SS_CMD_COMPUTE_DOT        0x01
#define SS_CMD_COMPUTE_ROW        0x02
#define SS_CMD_COMPUTE_BLOCK      0x03
#define SS_CMD_COMPUTE_PLANE      0x04
#define SS_CMD_COMPUTE_PIPE       0x05
#define SS_CMD_PROGRAM_WEIGHTS    0x06
#define SS_CMD_READ_WEIGHTS       0x07
#define SS_CMD_START_BIT          (1u << 4)

/**
 * Status register.
 * Bit [0] = Busy
 * Bit [1] = Done (latched until cleared)
 * Bit [2] = Error
 * Bit [3] = Weight programming complete
 * Bit [4] = ZID active
 */
#define SS_REG_STATUS             0x0C4

#define SS_STATUS_BUSY            (1u << 0)
#define SS_STATUS_DONE            (1u << 1)
#define SS_STATUS_ERROR           (1u << 2)
#define SS_STATUS_WPROG_DONE      (1u << 3)
#define SS_STATUS_ZID_ACTIVE      (1u << 4)

/**
 * Interrupt enable register.
 * Same bit layout as status register; set bit to enable interrupt.
 */
#define SS_REG_INT_ENABLE         0x0C8

/** Interrupt status (read to see which interrupts fired; write 1 to clear) */
#define SS_REG_INT_STATUS         0x0CC

/* ===================================================================== */
/* MMIO Access Helpers                                                   */
/* ===================================================================== */

/** Write a 32-bit value to an MMIO register */
static inline void ss_mmio_write(volatile uint32_t *base,
                                  uint32_t offset, uint32_t value)
{
    base[offset / 4] = value;
}

/** Read a 32-bit value from an MMIO register */
static inline uint32_t ss_mmio_read(const volatile uint32_t *base,
                                     uint32_t offset)
{
    return base[offset / 4];
}

#ifdef __cplusplus
}
#endif

#endif /* SET5_SAMSUNG_NAND_H */
