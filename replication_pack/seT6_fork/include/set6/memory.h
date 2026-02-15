/**
 * @file memory.h
 * @brief seT6 Physical Memory Manager — Ternary Page Allocator
 *
 * Manages physical memory as fixed-size pages of ternary trits.
 * Every page is initialised to Unknown (Kleene lattice middle element)
 * on allocation, and scrubbed back to Unknown on free — eliminating
 * use-after-free and uninitialized-data bugs by construction.
 *
 * Design (seL4-inspired):
 *   - Fixed-size pages (729 trits = 3^6, one tryte-page)
 *   - Ternary validity per page: T=allocated, U=free, F=reserved
 *   - Scrub-on-free guarantee: no stale data leakage across processes
 *   - Unknown-init guarantee: freshly mapped pages are all-Unknown
 *   - Memristive spill target: pages can be backed by 1T1M cells
 *
 * @see ARCHITECTURE.md §5 — Memory Model
 * @see init.c for bootstrap usage
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_MEMORY_H
#define SET6_MEMORY_H

#include "set6/trit.h"
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Configuration ---------------------------------------------------- */

/** Page size in trits (6-trit tryte → 3^6 = 729 states) */
#define SET6_PAGE_TRITS   729

/** Maximum physical pages */
#define SET6_MAX_PAGES    256

/** Page flags */
#define PAGE_FLAG_NONE       0
#define PAGE_FLAG_READONLY   1       /**< Page is read-only (COW) */
#define PAGE_FLAG_MEMRISTIVE 2       /**< Backed by memristive storage */
#define PAGE_FLAG_DEVICE     4       /**< Memory-mapped device I/O */

/* ---- Data Structures -------------------------------------------------- */

/** Physical page descriptor */
typedef struct {
    trit  data[SET6_PAGE_TRITS];     /**< Trit contents (Unknown-init) */
    trit  valid;                      /**< T=allocated, U=free, F=reserved */
    int   flags;                      /**< PAGE_FLAG_* bitmask */
    int   owner_tid;                  /**< Owning thread (-1 = kernel) */
    int   ref_count;                  /**< Reference count for sharing */
} set6_page_t;

/** Memory manager state */
typedef struct {
    set6_page_t pages[SET6_MAX_PAGES];
    int         total_pages;          /**< Configured page count */
    int         free_count;           /**< Number of free pages */
    int         alloc_count;          /**< Number of allocated pages */
} set6_mem_t;

/* ---- API -------------------------------------------------------------- */

/**
 * @brief Initialise the memory manager.
 *
 * Sets all pages to Unknown-valid (free), contents all-Unknown.
 *
 * @param mem        Pointer to memory manager state.
 * @param num_pages  Number of physical pages to manage (≤ SET6_MAX_PAGES).
 */
void mem_init(set6_mem_t *mem, int num_pages);

/**
 * @brief Allocate a physical page.
 *
 * Scans for first free page (valid == Unknown), marks it True (allocated),
 * assigns ownership, and guarantees all trits are Unknown-initialised.
 *
 * @param mem       Memory manager state.
 * @param owner_tid Thread ID to assign ownership (-1 for kernel).
 * @return Page index (>= 0) on success, -1 on OOM.
 */
int mem_alloc(set6_mem_t *mem, int owner_tid);

/**
 * @brief Free a physical page.
 *
 * Scrubs contents to all-Unknown (no stale data leakage), resets validity
 * to Unknown (free), clears ownership and flags.
 *
 * @param mem       Memory manager state.
 * @param page_idx  Page index to free.
 * @return 0 on success, -1 if invalid index or page already free.
 */
int mem_free(set6_mem_t *mem, int page_idx);

/**
 * @brief Read a trit from a page at a given offset.
 *
 * @param mem       Memory manager state.
 * @param page_idx  Page index.
 * @param offset    Trit offset within page (0..SET6_PAGE_TRITS-1).
 * @return Trit value, or TRIT_UNKNOWN if out of bounds / unallocated.
 */
trit mem_read(const set6_mem_t *mem, int page_idx, int offset);

/**
 * @brief Write a trit to a page at a given offset.
 *
 * Fails silently if page is read-only, out of bounds, or unallocated.
 *
 * @param mem       Memory manager state.
 * @param page_idx  Page index.
 * @param offset    Trit offset within page.
 * @param value     Trit value to write.
 * @return 0 on success, -1 on failure.
 */
int mem_write(set6_mem_t *mem, int page_idx, int offset, trit value);

/**
 * @brief Mark a page as reserved (kernel-only, not allocable).
 *
 * @param mem       Memory manager state.
 * @param page_idx  Page index to reserve.
 * @return 0 on success, -1 if invalid.
 */
int mem_reserve(set6_mem_t *mem, int page_idx);

/**
 * @brief Get allocation statistics.
 *
 * @param mem         Memory manager state.
 * @param[out] total  Total configured pages.
 * @param[out] free   Free pages.
 * @param[out] alloc  Allocated pages.
 */
void mem_stats(const set6_mem_t *mem, int *total, int *free, int *alloc);

/**
 * @brief Scrub a page: fill with Unknown without changing allocation state.
 *
 * Used for zeroing sensitive data in-place (e.g., after IPC).
 *
 * @param mem       Memory manager state.
 * @param page_idx  Page to scrub.
 * @return 0 on success, -1 if invalid.
 */
int mem_scrub(set6_mem_t *mem, int page_idx);

#ifdef __cplusplus
}
#endif

#endif /* SET6_MEMORY_H */
