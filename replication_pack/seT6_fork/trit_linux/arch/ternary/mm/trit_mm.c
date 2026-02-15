/**
 * @file trit_mm.c
 * @brief Trit Linux — Tryte-Aligned Memory Manager
 *
 * Implements the Linux-style page manager for the ternary architecture.
 * Wraps seT6's set6_mem_t with two-level ternary page tables for
 * virtual-to-physical address translation.
 *
 * Page table structure:
 *   Level 1: indexed by trits [11..9] of virtual page number (27 entries)
 *   Level 2: indexed by trits [8..6]  of virtual page number (27 entries)
 *   Total mappable pages: 27 × 27 = 729 (matches TRIT_MAX_PAGES)
 *
 * The index within each level is derived from the virtual page number:
 *   l1_idx = virt_page / 27     (0..26)
 *   l2_idx = virt_page % 27     (0..26)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "asm/trit_page.h"
#include <string.h>
#include <stdio.h>

/* ---- Page manager initialization -------------------------------------- */

void trit_page_mgr_init(trit_page_mgr_t *mgr, int num_pages) {
    if (!mgr) return;
    if (num_pages > SET6_MAX_PAGES) num_pages = SET6_MAX_PAGES;

    /* Initialize underlying seT6 memory */
    mem_init(&mgr->mem, num_pages);

    /* Clear page table */
    memset(&mgr->pt, 0, sizeof(mgr->pt));
    for (int i = 0; i < TRIT_PT_ENTRIES; i++) {
        for (int j = 0; j < TRIT_PT_ENTRIES; j++) {
            mgr->pt.level1[i].entries[j].phys_page = -1;
            mgr->pt.level1[i].entries[j].present = 0;
        }
    }
    mgr->pt.mapped_count = 0;

    mgr->total_pages = num_pages;
    mgr->free_pages = num_pages;
    mgr->fault_count = 0;
}

/* ---- Page allocation -------------------------------------------------- */

int trit_page_alloc(trit_page_mgr_t *mgr, int owner_tid) {
    if (!mgr) return -1;

    int page = mem_alloc(&mgr->mem, owner_tid);
    if (page >= 0) {
        mgr->free_pages--;
    }
    return page;
}

int trit_page_free(trit_page_mgr_t *mgr, int page_idx) {
    if (!mgr) return -1;

    int result = mem_free(&mgr->mem, page_idx);
    if (result == 0) {
        mgr->free_pages++;
    }
    return result;
}

/* ---- Page table operations -------------------------------------------- */

/** Convert virtual page number to two-level indices */
static void virt_to_indices(int virt_page, int *l1, int *l2) {
    /* Clamp to valid range */
    if (virt_page < 0) virt_page = 0;
    if (virt_page >= TRIT_MAX_PAGES) virt_page = TRIT_MAX_PAGES - 1;
    *l1 = virt_page / TRIT_PT_ENTRIES;
    *l2 = virt_page % TRIT_PT_ENTRIES;
}

int trit_page_map(trit_page_mgr_t *mgr, int virt_page, int phys_page,
                  int writable, int user) {
    if (!mgr) return -1;
    if (virt_page < 0 || virt_page >= TRIT_MAX_PAGES) return -1;
    if (phys_page < 0 || phys_page >= mgr->total_pages) return -1;

    int l1, l2;
    virt_to_indices(virt_page, &l1, &l2);

    trit_pte_t *pte = &mgr->pt.level1[l1].entries[l2];

    /* If already mapped to something else, unmap first */
    if (pte->present && pte->phys_page != phys_page) {
        mgr->pt.mapped_count--;
    }

    pte->phys_page = phys_page;
    pte->present = 1;
    pte->writable = writable;
    pte->user = user;

    if (!pte->present || pte->phys_page != phys_page) {
        mgr->pt.mapped_count++;
    }
    mgr->pt.mapped_count++;

    return 0;
}

int trit_page_unmap(trit_page_mgr_t *mgr, int virt_page) {
    if (!mgr) return -1;
    if (virt_page < 0 || virt_page >= TRIT_MAX_PAGES) return -1;

    int l1, l2;
    virt_to_indices(virt_page, &l1, &l2);

    trit_pte_t *pte = &mgr->pt.level1[l1].entries[l2];
    if (!pte->present) {
        mgr->fault_count++;
        return -1;  /* not mapped */
    }

    int phys = pte->phys_page;
    pte->phys_page = -1;
    pte->present = 0;
    pte->writable = 0;
    pte->user = 0;
    mgr->pt.mapped_count--;

    return phys;
}

int trit_page_translate(const trit_page_mgr_t *mgr, int virt_page) {
    if (!mgr) return -1;
    if (virt_page < 0 || virt_page >= TRIT_MAX_PAGES) return -1;

    int l1, l2;
    virt_to_indices(virt_page, &l1, &l2);

    const trit_pte_t *pte = &mgr->pt.level1[l1].entries[l2];
    if (!pte->present) return -1;  /* page fault */

    return pte->phys_page;
}

/* ---- Read/Write through page table ------------------------------------ */

trit trit_page_read(const trit_page_mgr_t *mgr, int virt_page, int offset) {
    if (!mgr) return TRIT_UNKNOWN;

    int phys = trit_page_translate(mgr, virt_page);
    if (phys < 0) return TRIT_UNKNOWN;  /* fault: return Unknown */

    return mem_read(&mgr->mem, phys, offset);
}

int trit_page_write(trit_page_mgr_t *mgr, int virt_page, int offset, trit value) {
    if (!mgr) return -1;

    int l1, l2;
    virt_to_indices(virt_page, &l1, &l2);

    const trit_pte_t *pte = &mgr->pt.level1[l1].entries[l2];
    if (!pte->present) {
        mgr->fault_count++;
        return -1;
    }
    if (!pte->writable) return -2;  /* read-only */

    return mem_write(&mgr->mem, pte->phys_page, offset, value);
}

/* ---- Statistics ------------------------------------------------------- */

void trit_page_stats(const trit_page_mgr_t *mgr, int *total, int *free,
                     int *mapped, int *faults) {
    if (!mgr) return;
    if (total)  *total  = mgr->total_pages;
    if (free)   *free   = mgr->free_pages;
    if (mapped) *mapped = mgr->pt.mapped_count;
    if (faults) *faults = mgr->fault_count;
}
