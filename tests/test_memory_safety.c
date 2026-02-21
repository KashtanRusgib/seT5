/**
 * @file test_memory_safety.c
 * @brief Memory Safety and Bounds Checking Tests for seT5
 *
 * Tests memory allocation, deallocation, bounds checking,
 * and scrub-on-free guarantees using the actual seT5 memory API.
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "set5/memory.h"
#include "set5/trit.h"

/* ---- Test harness ----------------------------------------------------- */

static int tests_run    = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define CHECK(desc, expr) do { \
    tests_run++; \
    if (expr) { \
        tests_passed++; \
        printf("  [PASS] %s\n", desc); \
    } else { \
        tests_failed++; \
        printf("  [FAIL] %s\n", desc); \
    } \
} while(0)

/* ==== Memory Safety Tests ============================================== */

void test_memory_allocation_bounds(void) {
    printf("Testing memory allocation bounds...\n");

    set5_mem_t mem;
    mem_init(&mem, 32);

    /* Allocate pages */
    int page1 = mem_alloc(&mem, 0);
    CHECK("Allocate page 1", page1 >= 0);

    int page2 = mem_alloc(&mem, 0);
    CHECK("Allocate page 2", page2 >= 0);

    /* Free */
    int r1 = mem_free(&mem, page1);
    CHECK("Free page 1", r1 == 0);

    int r2 = mem_free(&mem, page2);
    CHECK("Free page 2", r2 == 0);

    /* Double free should return error */
    int r3 = mem_free(&mem, page1);
    CHECK("Double free returns error", r3 == -1);
}

void test_memory_read_write(void) {
    printf("Testing memory read/write bounds...\n");

    set5_mem_t mem;
    mem_init(&mem, 16);

    int page = mem_alloc(&mem, 0);
    CHECK("Allocate page for read/write", page >= 0);

    /* Write within bounds */
    int wr = mem_write(&mem, page, 0, TRIT_TRUE);
    CHECK("Write within bounds", wr == 0);

    /* Read back */
    trit val = mem_read(&mem, page, 0);
    CHECK("Read matches write", val == TRIT_TRUE);

    /* Write at maximum offset */
    wr = mem_write(&mem, page, SET5_PAGE_TRITS - 1, TRIT_FALSE);
    CHECK("Write at max offset", wr == 0);

    /* Read at max offset */
    val = mem_read(&mem, page, SET5_PAGE_TRITS - 1);
    CHECK("Read at max offset", val == TRIT_FALSE);

    /* Out-of-bounds write should fail */
    wr = mem_write(&mem, page, SET5_PAGE_TRITS, TRIT_TRUE);
    CHECK("Out-of-bounds write rejected", wr == -1);

    /* Out-of-bounds read returns Unknown */
    val = mem_read(&mem, page, SET5_PAGE_TRITS);
    CHECK("Out-of-bounds read returns Unknown", val == TRIT_UNKNOWN);

    mem_free(&mem, page);
}

void test_scrub_on_free(void) {
    printf("Testing scrub-on-free guarantee...\n");

    set5_mem_t mem;
    mem_init(&mem, 16);

    int page = mem_alloc(&mem, 0);
    CHECK("Allocate page", page >= 0);

    /* Write known pattern */
    for (int i = 0; i < 10; i++) {
        mem_write(&mem, page, i, TRIT_TRUE);
    }

    trit val = mem_read(&mem, page, 0);
    CHECK("Pattern written", val == TRIT_TRUE);

    /* Scrub the page — caller TID 0 owns it (owner from mem_alloc call) */
    int sr = mem_scrub(&mem, page, 0);
    CHECK("Scrub succeeds", sr == 0);

    /* After scrub, all should be Unknown */
    int all_unknown = 1;
    for (int i = 0; i < 10; i++) {
        if (mem_read(&mem, page, i) != TRIT_UNKNOWN) {
            all_unknown = 0;
            break;
        }
    }
    CHECK("Scrub clears to Unknown", all_unknown);

    mem_free(&mem, page);
}

void test_allocation_exhaustion(void) {
    printf("Testing allocation exhaustion...\n");

    set5_mem_t mem;
    int num_pages = 8;
    mem_init(&mem, num_pages);

    /* Allocate all pages */
    int pages[8];
    int all_ok = 1;
    for (int i = 0; i < num_pages; i++) {
        pages[i] = mem_alloc(&mem, 0);
        if (pages[i] < 0) { all_ok = 0; break; }
    }
    CHECK("Allocate all pages", all_ok);

    /* Next allocation should fail (OOM) */
    int oom = mem_alloc(&mem, 0);
    CHECK("OOM returns -1", oom == -1);

    /* Free one and re-allocate */
    mem_free(&mem, pages[0]);
    int reuse = mem_alloc(&mem, 0);
    CHECK("Re-allocate after free", reuse >= 0);

    /* Clean up */
    for (int i = 1; i < num_pages; i++) {
        mem_free(&mem, pages[i]);
    }
    mem_free(&mem, reuse);
}

void test_memory_stats(void) {
    printf("Testing memory statistics...\n");

    set5_mem_t mem;
    mem_init(&mem, 16);

    int total, free_count, alloc_count;
    mem_stats(&mem, &total, &free_count, &alloc_count);
    CHECK("Initial total correct", total == 16);
    CHECK("Initial all free", free_count == 16);
    CHECK("Initial none allocated", alloc_count == 0);

    int page = mem_alloc(&mem, 0);
    mem_stats(&mem, &total, &free_count, &alloc_count);
    CHECK("After alloc: 1 allocated", alloc_count == 1);
    CHECK("After alloc: 15 free", free_count == 15);

    mem_free(&mem, page);
    mem_stats(&mem, &total, &free_count, &alloc_count);
    CHECK("After free: 0 allocated", alloc_count == 0);
    CHECK("After free: 16 free", free_count == 16);
}

void test_page_reservation(void) {
    printf("Testing page reservation...\n");

    set5_mem_t mem;
    mem_init(&mem, 16);

    /* Reserve page 0 */
    int rr = mem_reserve(&mem, 0);
    CHECK("Reserve page 0", rr == 0);

    /* Allocations should skip reserved pages */
    int page = mem_alloc(&mem, 0);
    CHECK("Allocation skips reserved page", page != 0 && page >= 0);

    mem_free(&mem, page);
}

int main(void) {
    printf("=== seT5 Memory Safety Tests ===\n\n");

    test_memory_allocation_bounds();
    test_memory_read_write();
    test_scrub_on_free();
    test_allocation_exhaustion();
    test_memory_stats();
    test_page_reservation();

    printf("\n=== Results: %d/%d passed", tests_passed, tests_run);
    if (tests_failed > 0) {
        printf(" (%d FAILED)", tests_failed);
    }
    printf(" ===\n");

    return tests_failed > 0 ? 1 : 0;
}
