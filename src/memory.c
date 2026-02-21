/**
 * @file memory.c
 * @brief seT5 Physical Memory Manager — Implementation
 *
 * Fixed-size page allocator with ternary validity tracking:
 *   - Unknown (0):  free, available for allocation
 *   - True (+1):    allocated, in-use
 *   - False (-1):   reserved (kernel, device, or memristive-backed)
 *
 * Security guarantees:
 *   1. Unknown-init: freshly allocated pages contain only TRIT_UNKNOWN
 *   2. Scrub-on-free: freed pages are wiped to TRIT_UNKNOWN
 *   3. No double-free: freeing a free page returns error
 *   4. No wild writes: writes to unallocated/reserved pages fail
 *
 * @see include/set5/memory.h for API documentation
 * @see ARCHITECTURE.md §5 — Memory Model
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/memory.h"
#include <string.h>

/* ==== Initialisation =================================================== */

void mem_init(set5_mem_t *mem, int num_pages) {
    if (!mem) return;
    if (num_pages > SET5_MAX_PAGES)
        num_pages = SET5_MAX_PAGES;
    if (num_pages < 0)
        num_pages = 0;

    mem->total_pages = num_pages;
    mem->free_count  = num_pages;
    mem->alloc_count = 0;

    for (int p = 0; p < SET5_MAX_PAGES; p++) {
        set5_page_t *pg = &mem->pages[p];
        /* All trits → Unknown (the "third" state, not a valid zero) */
        for (int i = 0; i < SET5_PAGE_TRITS; i++)
            pg->data[i] = TRIT_UNKNOWN;
        pg->valid     = (p < num_pages) ? TRIT_UNKNOWN : TRIT_FALSE;
        pg->flags     = PAGE_FLAG_NONE;
        pg->owner_tid = -1;
        pg->ref_count = 0;
    }
}

/* ==== Allocation ======================================================= */

int mem_alloc(set5_mem_t *mem, int owner_tid) {
    if (!mem) return -1;

    for (int p = 0; p < mem->total_pages; p++) {
        if (mem->pages[p].valid == TRIT_UNKNOWN) {
            set5_page_t *pg = &mem->pages[p];
            pg->valid     = TRIT_TRUE;
            pg->owner_tid = owner_tid;
            pg->ref_count = 1;
            pg->flags     = PAGE_FLAG_NONE;
            /* Unknown-init guarantee: data already all TRIT_UNKNOWN
             * from init or prior scrub-on-free */
            mem->free_count--;
            mem->alloc_count++;
            return p;
        }
    }
    return -1;  /* OOM: no free pages */
}

/* ==== Free ============================================================= */

int mem_free(set5_mem_t *mem, int page_idx) {
    if (!mem) return -1;
    if (page_idx < 0 || page_idx >= mem->total_pages) return -1;

    set5_page_t *pg = &mem->pages[page_idx];

    /* Only allocated pages can be freed */
    if (pg->valid != TRIT_TRUE) return -1;

    /* Decrement refcount; only actually free when it hits zero */
    pg->ref_count--;
    if (pg->ref_count > 0) return 0;  /* still shared */

    /* Scrub-on-free: wipe all trits to Unknown (security guarantee) */
    for (int i = 0; i < SET5_PAGE_TRITS; i++)
        pg->data[i] = TRIT_UNKNOWN;

    pg->valid     = TRIT_UNKNOWN;  /* back to free */
    pg->flags     = PAGE_FLAG_NONE;
    pg->owner_tid = -1;
    mem->free_count++;
    mem->alloc_count--;
    return 0;
}

/* ==== Read / Write ===================================================== */

trit mem_read(const set5_mem_t *mem, int page_idx, int offset) {
    if (!mem) return TRIT_UNKNOWN;
    if (page_idx < 0 || page_idx >= mem->total_pages) return TRIT_UNKNOWN;
    if (offset < 0 || offset >= SET5_PAGE_TRITS) return TRIT_UNKNOWN;

    const set5_page_t *pg = &mem->pages[page_idx];
    /* Reading from unallocated page returns Unknown (safe default) */
    if (pg->valid != TRIT_TRUE) return TRIT_UNKNOWN;

    return pg->data[offset];
}

int mem_write(set5_mem_t *mem, int page_idx, int offset, trit value) {
    if (!mem) return -1;
    if (page_idx < 0 || page_idx >= mem->total_pages) return -1;
    if (offset < 0 || offset >= SET5_PAGE_TRITS) return -1;

    set5_page_t *pg = &mem->pages[page_idx];

    /* Cannot write to unallocated, reserved, or read-only pages */
    if (pg->valid != TRIT_TRUE) return -1;
    if (pg->flags & PAGE_FLAG_READONLY) return -1;

    pg->data[offset] = value;
    return 0;
}

/* ==== Reserve ========================================================== */

int mem_reserve(set5_mem_t *mem, int page_idx) {
    if (!mem) return -1;
    if (page_idx < 0 || page_idx >= mem->total_pages) return -1;

    set5_page_t *pg = &mem->pages[page_idx];
    if (pg->valid == TRIT_TRUE) return -1;  /* can't reserve allocated */

    if (pg->valid == TRIT_UNKNOWN) {
        mem->free_count--;  /* was free, now reserved */
    }
    pg->valid     = TRIT_FALSE;  /* reserved */
    pg->owner_tid = -1;          /* kernel owns */
    return 0;
}

/* ==== Statistics ======================================================= */

void mem_stats(const set5_mem_t *mem, int *total, int *free, int *alloc) {
    if (!mem) return;
    if (total) *total = mem->total_pages;
    if (free)  *free  = mem->free_count;
    if (alloc) *alloc = mem->alloc_count;
}

/* ==== Scrub ============================================================ */

int mem_scrub(set5_mem_t *mem, int page_idx, int caller_tid) {
    if (!mem) return -1;
    if (page_idx < 0 || page_idx >= mem->total_pages) return -1;

    set5_page_t *pg = &mem->pages[page_idx];
    /* VULN-52 fix: deny scrubbing of reserved (kernel/device) pages.
     * Allocated (TRIT_TRUE) pages may be scrubbed by kernel authority
     * (the kernel itself calls this). User-space access to scrub
     * must be gated by a capability check in the syscall layer. */
    if (pg->valid == TRIT_FALSE) return -1;  /* reserved — deny */

    /* VULN-56 fix: ownership check — only the page owner or kernel
     * (caller_tid == -1) may scrub an allocated page. Eliminates
     * cross-process data destruction without a capability. */
    if (caller_tid != -1 && pg->valid == TRIT_TRUE &&
        pg->owner_tid != caller_tid) return -1;

    for (int i = 0; i < SET5_PAGE_TRITS; i++)
        pg->data[i] = TRIT_UNKNOWN;
    return 0;
}
