/**
 * @file samsung_tseq_mmio.h
 * @brief MMIO Register Map for Samsung CN105745888A Ternary Sequence Modem
 *
 * Hypothetical hardware register layout for a dedicated ternary sequence
 * modem implementing the CN105745888A protocol.  The modem accelerates
 * correlation-based demodulation in hardware, matching the patent's
 * receiver architecture (Fig. 10).
 *
 * Register aperture: 4 KB at base address 0x40300000.
 *
 * Layout:
 *   0x000 – 0x00F  Chip identification
 *   0x010 – 0x01F  Mode / configuration
 *   0x020 – 0x03F  Base sequence programming
 *   0x040 – 0x05F  TX control & symbol input
 *   0x060 – 0x07F  RX control & correlation output
 *   0x080 – 0x09F  Codeset / reference cache control
 *   0x0A0 – 0x0BF  Frame & timing
 *   0x0C0 – 0x0DF  Status / command
 *   0x100 – 0x1FF  Base sequence data (write: load, read: current)
 *   0x200 – 0x2FF  TX sequence output buffer
 *   0x300 – 0x3FF  RX sequence input buffer
 *
 * @see samsung_tseq.h       for sequence types
 * @see samsung_tseq_modem.h for modem API
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_SAMSUNG_TSEQ_MMIO_H
#define SET6_SAMSUNG_TSEQ_MMIO_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ===================================================================== */
/* Base Address                                                          */
/* ===================================================================== */

#define TSEQ_MMIO_BASE         0x40300000UL
#define TSEQ_MMIO_SIZE         0x1000      /* 4 KB aperture */

/* ===================================================================== */
/* Chip Identification (0x000 – 0x00F)                                   */
/* ===================================================================== */

#define TSEQ_REG_CHIP_ID       0x000   /**< RO: Chip ID word          */
#define TSEQ_REG_CHIP_REV      0x004   /**< RO: Silicon revision      */
#define TSEQ_REG_PATENT_ID     0x008   /**< RO: Patent ref (0x105745) */

/** Expected values */
#define TSEQ_CHIP_ID_VALUE     0x534D5451UL  /* "SMTQ" Samsung Ternary seQ */
#define TSEQ_CHIP_REV_A0       0x00000A00UL
#define TSEQ_PATENT_ID_VALUE   0x00105745UL  /* CN105745888A */

/* ===================================================================== */
/* Mode / Configuration (0x010 – 0x01F)                                  */
/* ===================================================================== */

#define TSEQ_REG_MODE          0x010   /**< RW: Operating mode        */
#define TSEQ_REG_FAMILY        0x014   /**< RW: OOK family selector   */
#define TSEQ_REG_MAP_TYPE      0x018   /**< RW: Symbol mapping type   */

/** Mode register bits */
#define TSEQ_MODE_ENABLE       (1U << 0)   /**< Modem enable          */
#define TSEQ_MODE_TX           (1U << 1)   /**< TX mode active        */
#define TSEQ_MODE_RX           (1U << 2)   /**< RX mode active        */
#define TSEQ_MODE_COHERENT     (1U << 3)   /**< 1=coherent, 0=non-coh */
#define TSEQ_MODE_AUTO_CORR    (1U << 4)   /**< HW auto-correlation   */
#define TSEQ_MODE_IRQ_EN       (1U << 8)   /**< Interrupt enable      */

/** Family register values */
#define TSEQ_FAMILY_REG_3_8    0x00000308UL  /* k=3, N=8  */
#define TSEQ_FAMILY_REG_4_16   0x00000410UL  /* k=4, N=16 */
#define TSEQ_FAMILY_REG_5_32   0x00000520UL  /* k=5, N=32 */

/** Mapping type register values */
#define TSEQ_MAP_REG_DECIMAL   0x00000000UL
#define TSEQ_MAP_REG_GRAY      0x00000001UL

/* ===================================================================== */
/* Base Sequence Programming (0x020 – 0x03F)                             */
/* ===================================================================== */

#define TSEQ_REG_BASE_LEN      0x020   /**< RW: Base sequence length  */
#define TSEQ_REG_BASE_LOAD     0x024   /**< WO: Write 1 to load seq   */
#define TSEQ_REG_BASE_STATUS   0x028   /**< RO: Load status           */
#define TSEQ_REG_BASE_MSAC     0x02C   /**< RO: MSAC of loaded seq    */
#define TSEQ_REG_BASE_MSAC_ABS 0x030   /**< RO: MSAC of |seq|         */
#define TSEQ_REG_BASE_WEIGHT   0x034   /**< RO: Weight of sequence    */

/** Base status bits */
#define TSEQ_BASE_LOADED       (1U << 0)
#define TSEQ_BASE_VALID        (1U << 1)
#define TSEQ_BASE_PERFECT      (1U << 2)

/* ===================================================================== */
/* TX Control (0x040 – 0x05F)                                            */
/* ===================================================================== */

#define TSEQ_REG_TX_SYMBOL     0x040   /**< WO: Symbol to transmit    */
#define TSEQ_REG_TX_START      0x044   /**< WO: Write 1 to start TX   */
#define TSEQ_REG_TX_STATUS     0x048   /**< RO: TX status             */
#define TSEQ_REG_TX_COUNT      0x04C   /**< RO: Total symbols sent    */
#define TSEQ_REG_TX_SHIFT      0x050   /**< RO: Last cyclic shift g   */

/** TX status bits */
#define TSEQ_TX_BUSY           (1U << 0)
#define TSEQ_TX_DONE           (1U << 1)
#define TSEQ_TX_ERROR          (1U << 2)

/* ===================================================================== */
/* RX Control & Correlation (0x060 – 0x07F)                              */
/* ===================================================================== */

#define TSEQ_REG_RX_START      0x060   /**< WO: Write 1 to start RX   */
#define TSEQ_REG_RX_STATUS     0x064   /**< RO: RX status             */
#define TSEQ_REG_RX_BEST_SHIFT 0x068   /**< RO: g_est = argmax        */
#define TSEQ_REG_RX_MAX_CORR   0x06C   /**< RO: Maximum Corr value    */
#define TSEQ_REG_RX_SYMBOL     0x070   /**< RO: Detected symbol       */
#define TSEQ_REG_RX_COUNT      0x074   /**< RO: Total symbols received*/
#define TSEQ_REG_RX_CORR_IDX   0x078   /**< WO: Select corr index g   */
#define TSEQ_REG_RX_CORR_VAL   0x07C   /**< RO: Corr value for idx    */

/** RX status bits */
#define TSEQ_RX_BUSY           (1U << 0)
#define TSEQ_RX_DONE           (1U << 1)
#define TSEQ_RX_SYMBOL_VALID   (1U << 2)
#define TSEQ_RX_ERROR          (1U << 3)

/* ===================================================================== */
/* Codeset / Reference Cache (0x080 – 0x09F)                             */
/* ===================================================================== */

#define TSEQ_REG_CACHE_CTRL    0x080   /**< WO: Cache control         */
#define TSEQ_REG_CACHE_STATUS  0x084   /**< RO: Cache status          */

/** Cache control bits */
#define TSEQ_CACHE_REBUILD     (1U << 0)  /**< Rebuild codeset from base */
#define TSEQ_CACHE_FLUSH       (1U << 1)  /**< Flush cache             */
#define TSEQ_CACHE_ABS_MODE    (1U << 2)  /**< Build |base| ref set    */

/** Cache status bits */
#define TSEQ_CACHE_READY       (1U << 0)
#define TSEQ_CACHE_BUILDING    (1U << 1)

/* ===================================================================== */
/* Frame & Timing (0x0A0 – 0x0BF)                                       */
/* ===================================================================== */

#define TSEQ_REG_FRAME_LEN     0x0A0   /**< RW: Symbols per frame     */
#define TSEQ_REG_CHIP_DURATION 0x0A4   /**< RW: Tc in clock cycles    */
#define TSEQ_REG_SYMBOL_PERIOD 0x0A8   /**< RW: Symbol period clocks  */
#define TSEQ_REG_FRAME_COUNT   0x0AC   /**< RO: Frames TX/RX count    */

/* ===================================================================== */
/* Status / Command (0x0C0 – 0x0DF)                                      */
/* ===================================================================== */

#define TSEQ_REG_STATUS        0x0C0   /**< RO: Global status         */
#define TSEQ_REG_COMMAND       0x0C4   /**< WO: Command register      */
#define TSEQ_REG_IRQ_STATUS    0x0C8   /**< RO/W1C: Interrupt status  */
#define TSEQ_REG_IRQ_MASK      0x0CC   /**< RW: Interrupt mask        */
#define TSEQ_REG_ERROR_CODE    0x0D0   /**< RO: Last error code       */

/** Status bits */
#define TSEQ_STATUS_READY      (1U << 0)
#define TSEQ_STATUS_BUSY       (1U << 1)
#define TSEQ_STATUS_ERROR      (1U << 2)

/** Command codes (write to TSEQ_REG_COMMAND) */
#define TSEQ_CMD_RESET         0x00000001UL  /**< Soft reset           */
#define TSEQ_CMD_LOAD_BASE     0x00000002UL  /**< Load base from buf   */
#define TSEQ_CMD_BUILD_CODESET 0x00000003UL  /**< Build codeset        */
#define TSEQ_CMD_TX_SYMBOL     0x00000010UL  /**< Modulate & transmit  */
#define TSEQ_CMD_TX_FRAME      0x00000011UL  /**< TX entire frame      */
#define TSEQ_CMD_RX_DEMOD      0x00000020UL  /**< Demodulate one seq   */
#define TSEQ_CMD_RX_FRAME      0x00000021UL  /**< Demodulate frame     */
#define TSEQ_CMD_CORRELATE     0x00000030UL  /**< Run all correlations */

/** IRQ bits */
#define TSEQ_IRQ_TX_DONE       (1U << 0)
#define TSEQ_IRQ_RX_DONE       (1U << 1)
#define TSEQ_IRQ_FRAME_DONE    (1U << 2)
#define TSEQ_IRQ_ERROR         (1U << 3)

/* ===================================================================== */
/* Data Buffers                                                          */
/* ===================================================================== */

#define TSEQ_BUF_BASE_SEQ      0x100   /**< Base sequence data        */
#define TSEQ_BUF_BASE_SEQ_END  0x1FF
#define TSEQ_BUF_TX_OUT        0x200   /**< TX output buffer          */
#define TSEQ_BUF_TX_OUT_END    0x2FF
#define TSEQ_BUF_RX_IN         0x300   /**< RX input buffer           */
#define TSEQ_BUF_RX_IN_END     0x3FF

/* ===================================================================== */
/* Emulated Register State (for testing without real hardware)           */
/* ===================================================================== */

/**
 * Emulated MMIO state — mirrors all HW registers in software.
 */
typedef struct {
    uint32_t chip_id;
    uint32_t chip_rev;
    uint32_t patent_id;
    uint32_t mode;
    uint32_t family;
    uint32_t map_type;
    uint32_t base_len;
    uint32_t base_status;
    uint32_t base_weight;
    uint32_t tx_status;
    uint32_t tx_count;
    uint32_t tx_last_shift;
    uint32_t rx_status;
    uint32_t rx_best_shift;
    int32_t  rx_max_corr;
    uint32_t rx_symbol;
    uint32_t rx_count;
    uint32_t cache_status;
    uint32_t frame_len;
    uint32_t chip_duration;
    uint32_t symbol_period;
    uint32_t frame_count;
    uint32_t status;
    uint32_t irq_status;
    uint32_t irq_mask;
    uint32_t error_code;
    int8_t   base_buf[TSEQ_MAX_LEN];   /**< Base sequence data      */
    int8_t   tx_buf[TSEQ_MAX_LEN];     /**< TX output buffer        */
    int8_t   rx_buf[TSEQ_MAX_LEN];     /**< RX input buffer         */
} tseq_emu_regs_t;

/**
 * Initialise emulated registers to power-on defaults.
 */
static inline void tseq_emu_init(tseq_emu_regs_t *regs)
{
    regs->chip_id    = TSEQ_CHIP_ID_VALUE;
    regs->chip_rev   = TSEQ_CHIP_REV_A0;
    regs->patent_id  = TSEQ_PATENT_ID_VALUE;
    regs->mode       = 0;
    regs->family     = TSEQ_FAMILY_REG_3_8;
    regs->map_type   = TSEQ_MAP_REG_DECIMAL;
    regs->base_len   = 0;
    regs->base_status = 0;
    regs->base_weight = 0;
    regs->tx_status  = 0;
    regs->tx_count   = 0;
    regs->tx_last_shift = 0;
    regs->rx_status  = 0;
    regs->rx_best_shift = 0;
    regs->rx_max_corr = 0;
    regs->rx_symbol  = 0;
    regs->rx_count   = 0;
    regs->cache_status = 0;
    regs->frame_len  = 1;
    regs->chip_duration = 100;
    regs->symbol_period = 1000;
    regs->frame_count = 0;
    regs->status     = TSEQ_STATUS_READY;
    regs->irq_status = 0;
    regs->irq_mask   = 0;
    regs->error_code = 0;

    for (int i = 0; i < TSEQ_MAX_LEN; i++) {
        regs->base_buf[i] = 0;
        regs->tx_buf[i]   = 0;
        regs->rx_buf[i]   = 0;
    }
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_SAMSUNG_TSEQ_MMIO_H */
