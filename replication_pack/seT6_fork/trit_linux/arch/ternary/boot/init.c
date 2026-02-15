/**
 * @file init.c
 * @brief Trit Linux — Boot Entry Point
 *
 * Ternary architecture boot sequence:
 *   1. Initialize kernel state (seT6 memory + IPC + scheduler)
 *   2. Set up tryte-aligned page allocator (729-trit pages)
 *   3. Start trit-priority scheduler (-1/0/+1 levels)
 *   4. Initialize multi-radix engine (FFT/dot product)
 *   5. Validate ternary logic (consensus self-check)
 *   6. Hand off to TBE/Trithon init
 *
 * This file bridges Linux kernel conventions with seT6 primitives.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "asm/trit_types.h"
#include "asm/trit_page.h"
#include "set6/syscall.h"
#include "set6/multiradix.h"
#include "set6/trit.h"
#include <stdio.h>
#include <string.h>

/* ---- Forward declarations from kernel/trit_drivers.c ------------------ */
extern void trit_drivers_init(void);
extern int  trit_drivers_load_all(void);
extern void trit_drivers_report(void);
extern int  trit_drivers_count(void);

/* ---- Boot state ------------------------------------------------------- */

/** Global kernel state — initialized at boot */
static kernel_state_t  boot_kernel;
static trit_page_mgr_t boot_page_mgr;

/** Boot flags */
static int boot_mem_ok;
static int boot_sched_ok;
static int boot_mr_ok;
static int boot_logic_ok;
static int boot_pages_ok;

/* ---- Subsystem init --------------------------------------------------- */

/** Initialize ternary memory (tryte pages) */
static int trit_mem_boot(int num_pages) {
    mem_init(&boot_kernel.mem, num_pages);

    int total, free_count, alloc;
    mem_stats(&boot_kernel.mem, &total, &free_count, &alloc);
    return (total == num_pages && free_count == num_pages) ? 0 : -1;
}

/** Initialize trit-priority scheduler */
static int trit_sched_boot(void) {
    sched_init(&boot_kernel.sched);

    /* Create idle thread at low priority */
    int idle_tid = sched_create(&boot_kernel.sched, 0, TRIT_PRIO_LOW);
    if (idle_tid < 0) return -1;

    /* Create init thread at normal priority */
    int init_tid = sched_create(&boot_kernel.sched, 1, TRIT_PRIO_NORMAL);
    if (init_tid < 0) return -1;

    return 0;
}

/** Initialize multi-radix engine */
static int trit_mr_boot(void) {
    multiradix_init(&boot_kernel.mr);

    /* Verify radix conversion round-trip: 42 → ternary → binary */
    radix_conv_to_ternary(&boot_kernel.mr, 0, 42);
    int back = radix_conv_to_binary(&boot_kernel.mr, 0, 8);
    return (back == 42) ? 0 : -1;
}

/** Initialize IPC subsystem */
static void trit_ipc_boot(void) {
    ipc_init(&boot_kernel.ipc);
}

/** Self-check: verify Kleene logic consistency */
static int trit_logic_selfcheck(void) {
    /* Consensus: T AND F = F */
    if (trit_and(TRIT_TRUE, TRIT_FALSE) != TRIT_FALSE) return -1;

    /* Accept-any: T OR F = T */
    if (trit_or(TRIT_TRUE, TRIT_FALSE) != TRIT_TRUE) return -1;

    /* NOT involution: NOT(NOT(T)) = T */
    if (trit_not(trit_not(TRIT_TRUE)) != TRIT_TRUE) return -1;

    /* Unknown propagation: T AND U = U */
    if (trit_and(TRIT_TRUE, TRIT_UNKNOWN) != TRIT_UNKNOWN) return -1;

    /* Implies: F → anything = T */
    if (trit_implies(TRIT_FALSE, TRIT_FALSE) != TRIT_TRUE) return -1;

    return 0;
}

/** Initialize tryte page manager */
static int trit_pages_boot(int num_pages) {
    trit_page_mgr_init(&boot_page_mgr, num_pages);

    int total, free_count, mapped, faults;
    trit_page_stats(&boot_page_mgr, &total, &free_count, &mapped, &faults);
    return (total == num_pages && free_count == num_pages) ? 0 : -1;
}

/* ---- Public boot API -------------------------------------------------- */

/**
 * @brief Main boot entry for the ternary architecture.
 *
 * Initializes all kernel subsystems and validates the ternary
 * execution environment. Returns 0 on success, -1 on failure.
 */
int trit_boot(int num_pages) {
    printf("Trit Linux booting on seT6...\n");

    /* Step 1: Memory */
    boot_mem_ok = (trit_mem_boot(num_pages) == 0);
    printf("  [%s] Memory: %d tryte pages\n",
           boot_mem_ok ? "OK" : "FAIL", num_pages);

    /* Step 2: Scheduler */
    boot_sched_ok = (trit_sched_boot() == 0);
    printf("  [%s] Scheduler: trit priorities (-1/0/+1)\n",
           boot_sched_ok ? "OK" : "FAIL");

    /* Step 3: IPC */
    trit_ipc_boot();
    printf("  [OK] IPC: synchronous endpoints + notifications\n");

    /* Step 4: Multi-radix engine */
    boot_mr_ok = (trit_mr_boot() == 0);
    printf("  [%s] Multi-radix: FFT + dot product\n",
           boot_mr_ok ? "OK" : "FAIL");

    /* Step 5: Logic self-check */
    boot_logic_ok = (trit_logic_selfcheck() == 0);
    printf("  [%s] Kleene logic: consensus, accept-any, implies\n",
           boot_logic_ok ? "OK" : "FAIL");

    /* Step 6: Page manager */
    boot_pages_ok = (trit_pages_boot(num_pages) == 0);
    printf("  [%s] Page manager: tryte-aligned (%d-trit pages)\n",
           boot_pages_ok ? "OK" : "FAIL", TRYTE_PAGE_SIZE);

    /* Step 7: Functional utility module drivers */
    trit_drivers_init();
    int drv_loaded = trit_drivers_load_all();
    printf("  [%s] Module drivers: %d/%d loaded\n",
           (drv_loaded == trit_drivers_count()) ? "OK" : "WARN",
           drv_loaded, trit_drivers_count());
    trit_drivers_report();

    /* Report */
    int ok = boot_mem_ok && boot_sched_ok && boot_mr_ok &&
             boot_logic_ok && boot_pages_ok;
    printf("Trit Linux boot %s.\n", ok ? "complete" : "FAILED");

    return ok ? 0 : -1;
}

/**
 * @brief Emulation fallback — called when trit hardware is absent.
 *
 * Verifies the software emulation layer produces correct results.
 */
int trit_emu_fallback(void) {
    trit2 a = trit2_encode(1);   /* True */
    trit2 b = trit2_encode(-1);  /* False */

    /* AND(T, F) = F */
    trit2 r = trit2_and(a, b);
    if (trit2_decode(r) != -1) return -1;

    /* OR(T, F) = T */
    r = trit2_or(a, b);
    if (trit2_decode(r) != 1) return -1;

    /* NOT(T) = F */
    r = trit2_not(a);
    if (trit2_decode(r) != -1) return -1;

    /* 32-trit register operations */
    trit2_reg32 rt = trit2_reg32_splat(TRIT2_TRUE);
    trit2_reg32 rf = trit2_reg32_splat(TRIT2_FALSE);
    trit2_reg32 rr = trit2_reg32_and(rt, rf);

    /* Every trit should be FALSE */
    for (int i = 0; i < 32; i++) {
        if (trit2_decode(trit2_reg32_get(&rr, i)) != -1) return -1;
    }

    return 0;
}

/* ---- Query boot state ------------------------------------------------- */

int trit_boot_mem_ok(void)    { return boot_mem_ok; }
int trit_boot_sched_ok(void)  { return boot_sched_ok; }
int trit_boot_mr_ok(void)     { return boot_mr_ok; }
int trit_boot_logic_ok(void)  { return boot_logic_ok; }
int trit_boot_pages_ok(void)  { return boot_pages_ok; }

kernel_state_t *trit_boot_kernel(void) { return &boot_kernel; }
trit_page_mgr_t *trit_boot_page_mgr(void) { return &boot_page_mgr; }
