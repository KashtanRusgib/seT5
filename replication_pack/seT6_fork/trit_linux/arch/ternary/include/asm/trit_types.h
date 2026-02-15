/**
 * @file trit_types.h
 * @brief Trit Linux — Architecture-Level Ternary Types
 *
 * Defines ternary address types, tryte constants, and register
 * widths for the balanced ternary architecture.
 *
 * Address space: 12-trit addresses → 3^12 = 531 441 locations
 * Page size:     6-trit tryte     → 3^6  = 729 trits per page
 * Register:      32 trits packed in uint64_t (trit2_reg32)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_TYPES_H
#define TRIT_LINUX_TRIT_TYPES_H

#include "set6/trit.h"
#include "set6/trit_emu.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Address space geometry ------------------------------------------- */

/** Number of trits in a ternary address */
#define TRIT_ADDR_TRITS     12

/** Total addressable locations: 3^12 = 531441 */
#define TRIT_ADDR_SPACE     531441

/** Trits per page (one tryte = 3^6 = 729) */
#define TRYTE_PAGE_SIZE     729

/** Tryte page shift (6 trits per tryte) */
#define TRYTE_PAGE_SHIFT    6

/** Maximum pages in address space: 531441 / 729 = 729 */
#define TRIT_MAX_PAGES      729

/** Page table levels: 12 trits / 6 per level = 2 levels */
#define TRIT_PT_LEVELS      2

/** Entries per page table node: 3^3 = 27 (3-way branch at each trit) */
#define TRIT_PT_ENTRIES     27

/* ---- Ternary address type --------------------------------------------- */

/**
 * Balanced ternary address — 12 trits stored as an array.
 * Trit 0 is most significant.
 */
typedef struct {
    trit digits[TRIT_ADDR_TRITS];
} trit_addr_t;

/** Convert integer to ternary address (balanced representation) */
static inline trit_addr_t trit_addr_from_int(int value) {
    trit_addr_t addr;
    int v = value;
    for (int i = TRIT_ADDR_TRITS - 1; i >= 0; i--) {
        int rem = ((v % 3) + 3) % 3;  /* always positive mod */
        if (rem == 0)      { addr.digits[i] = 0;  v = v / 3; }
        else if (rem == 1) { addr.digits[i] = 1;  v = (v - 1) / 3; }
        else               { addr.digits[i] = -1; v = (v + 1) / 3; }
    }
    return addr;
}

/** Convert ternary address back to integer */
static inline int trit_addr_to_int(trit_addr_t addr) {
    int result = 0;
    int power = 1;
    for (int i = TRIT_ADDR_TRITS - 1; i >= 0; i--) {
        result += addr.digits[i] * power;
        power *= 3;
    }
    return result;
}

/** Add two ternary addresses with carry propagation */
static inline trit_addr_t trit_addr_add(trit_addr_t a, trit_addr_t b) {
    /* Simple: convert → add → convert back */
    int va = trit_addr_to_int(a);
    int vb = trit_addr_to_int(b);
    return trit_addr_from_int(va + vb);
}

/** Extract page index from address (upper 6 trits → 0..728) */
static inline int trit_addr_page(trit_addr_t addr) {
    int result = 0, power = 1;
    for (int i = TRIT_ADDR_TRITS - 1; i >= TRYTE_PAGE_SHIFT; i--) {
        result += addr.digits[i] * power;
        power *= 3;
    }
    return result;
}

/** Extract offset within page (lower 6 trits → 0..728) */
static inline int trit_addr_offset(trit_addr_t addr) {
    int result = 0, power = 1;
    for (int i = TRYTE_PAGE_SHIFT - 1; i >= 0; i--) {
        result += addr.digits[i] * power;
        power *= 3;
    }
    return result;
}

/* ---- Scheduler priority type ------------------------------------------ */

/** Trit priority: +1 = high (RT), 0 = normal, -1 = low (background) */
typedef trit trit_prio_t;

#define TRIT_PRIO_HIGH      TRIT_TRUE
#define TRIT_PRIO_NORMAL    TRIT_UNKNOWN
#define TRIT_PRIO_LOW       TRIT_FALSE

/* ---- Architecture feature flags --------------------------------------- */

#define TRIT_FEAT_SIMD      (1 << 0)   /**< 32-trit SIMD registers */
#define TRIT_FEAT_FFT       (1 << 1)   /**< Hardware FFT step */
#define TRIT_FEAT_DOTPROD   (1 << 2)   /**< Hardware dot product */
#define TRIT_FEAT_SPARSE    (1 << 3)   /**< N:M structured sparsity */
#define TRIT_FEAT_RADIXCONV (1 << 4)   /**< Binary ↔ ternary conversion */
#define TRIT_FEAT_MEMRISTIVE (1 << 5)  /**< Memristive memory backing */

/* ---- Functional utility module features (INCREASE_FUNCTIONAL_UTILITY) - */
#define TRIT_FEAT_TWQ       (1 << 6)   /**< Ternary Weight Quantizer */
#define TRIT_FEAT_DLFET     (1 << 7)   /**< DLFET-RM gate simulator */
#define TRIT_FEAT_SRBC      (1 << 8)   /**< Self-Referential Bias Calibration */
#define TRIT_FEAT_TCRYPTO   (1 << 9)   /**< Ternary cryptographic hardening */
#define TRIT_FEAT_PDELAY    (1 << 10)  /**< Propagation delay model */
#define TRIT_FEAT_TTL       (1 << 11)  /**< Ternary Temporal Logic */
#define TRIT_FEAT_PAM3      (1 << 12)  /**< PAM-3/4 interconnect */
#define TRIT_FEAT_TFA       (1 << 13)  /**< Ternary Full Adder (HW) */
#define TRIT_FEAT_WALLACE   (1 << 14)  /**< Wallace Tree Multiplier (HW) */

/* ---- Friday Updates (STT-MRAM, T-IPC, TFS) --------------------------- */
#define TRIT_FEAT_MRAM      (1 << 15)  /**< STT-MRAM Biaxial MTJ memory */
#define TRIT_FEAT_TIPC      (1 << 16)  /**< Ternary-Native IPC (Huffman) */
#define TRIT_FEAT_TFS       (1 << 17)  /**< Ternary-Native File System */

/** All features available in emulation */
#define TRIT_FEAT_ALL       (TRIT_FEAT_SIMD | TRIT_FEAT_FFT | \
                             TRIT_FEAT_DOTPROD | TRIT_FEAT_SPARSE | \
                             TRIT_FEAT_RADIXCONV | TRIT_FEAT_TWQ | \
                             TRIT_FEAT_DLFET | TRIT_FEAT_SRBC | \
                             TRIT_FEAT_TCRYPTO | TRIT_FEAT_PDELAY | \
                             TRIT_FEAT_TTL | TRIT_FEAT_PAM3 | \
                             TRIT_FEAT_TFA | TRIT_FEAT_WALLACE | \
                             TRIT_FEAT_MRAM | TRIT_FEAT_TIPC | \
                             TRIT_FEAT_TFS)

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_TYPES_H */
