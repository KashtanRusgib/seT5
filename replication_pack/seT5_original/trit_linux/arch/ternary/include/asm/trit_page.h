/**
 * @file trit_page.h
 * @brief Trit Linux — Tryte-Aligned Page Allocator
 *
 * Page allocator for the ternary architecture using 729-trit (tryte)
 * pages. Wraps the seT5 memory manager with Linux-kernel-style
 * interfaces and adds ternary page tables for virtual→physical mapping.
 *
 * Page table structure:
 *   2-level trit page tables, each level indexes 3 trit positions
 *   with 27 entries per node (3^3). Lookups walk trits from MSB.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRIT_LINUX_TRIT_PAGE_H
#define TRIT_LINUX_TRIT_PAGE_H

#include "asm/trit_types.h"
#include "set5/memory.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Page table node -------------------------------------------------- */

/** Page table entry: maps a 3-trit index to either next-level or phys page */
typedef struct {
    int  phys_page;     /**< Physical page index (-1 = unmapped) */
    int  present;       /**< 1 = valid mapping, 0 = not present */
    int  writable;      /**< 1 = read-write, 0 = read-only */
    int  user;          /**< 1 = user-accessible, 0 = kernel-only */
} trit_pte_t;

/** Page table node: 27 entries (3^3 combinations for 3-trit index) */
typedef struct {
    trit_pte_t entries[TRIT_PT_ENTRIES];
} trit_pt_node_t;

/** Two-level page table */
typedef struct {
    trit_pt_node_t level1[TRIT_PT_ENTRIES];  /**< First level (upper trits) */
    int            mapped_count;              /**< Total mapped pages */
} trit_page_table_t;

/* ---- Page manager state ----------------------------------------------- */

/** Linux-style page manager wrapping seT5 memory */
typedef struct {
    set5_mem_t        mem;              /**< Underlying seT5 page store */
    trit_page_table_t pt;               /**< Two-level page table */
    int               total_pages;      /**< Total managed pages */
    int               free_pages;       /**< Available pages */
    int               fault_count;      /**< Page fault counter */
} trit_page_mgr_t;

/* ---- API -------------------------------------------------------------- */

/** Initialize the page manager with the given number of pages */
void trit_page_mgr_init(trit_page_mgr_t *mgr, int num_pages);

/** Allocate a page, returns physical page index or -1 on failure */
int trit_page_alloc(trit_page_mgr_t *mgr, int owner_tid);

/** Free a page by physical index, returns 0 on success */
int trit_page_free(trit_page_mgr_t *mgr, int page_idx);

/** Map virtual page → physical page in the page table */
int trit_page_map(trit_page_mgr_t *mgr, int virt_page, int phys_page,
                  int writable, int user);

/** Unmap a virtual page, returns the physical page that was mapped */
int trit_page_unmap(trit_page_mgr_t *mgr, int virt_page);

/** Translate virtual page to physical page via page table walk */
int trit_page_translate(const trit_page_mgr_t *mgr, int virt_page);

/** Read a trit from a virtual address (page + offset) */
trit trit_page_read(const trit_page_mgr_t *mgr, int virt_page, int offset);

/** Write a trit to a virtual address (page + offset) */
int trit_page_write(trit_page_mgr_t *mgr, int virt_page, int offset, trit value);

/** Get page statistics */
void trit_page_stats(const trit_page_mgr_t *mgr, int *total, int *free,
                     int *mapped, int *faults);

#ifdef __cplusplus
}
#endif

#endif /* TRIT_LINUX_TRIT_PAGE_H */
