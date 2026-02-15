/**
 * @file setup.c
 * @brief Trit Linux — Architecture Setup (IRQ, Timer, CPU Features)
 *
 * Provides Linux-kernel-style arch setup functions for the ternary
 * architecture. In emulation mode, IRQs and timers are software-only.
 *
 * CPU feature detection reports which ternary ISA extensions are
 * available (SIMD, FFT, dot product, sparsity, radix conversion).
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "asm/trit_types.h"
#include "set5/trit.h"
#include "set5/trit_emu.h"
#include "set5/multiradix.h"
#include <stdio.h>
#include <string.h>

/* ---- IRQ subsystem ---------------------------------------------------- */

/** Maximum number of IRQ vectors */
#define TRIT_MAX_IRQS   27   /* 3^3 = ternary-indexed */

/** IRQ handler function type */
typedef void (*trit_irq_handler_t)(int irq_num);

/** IRQ descriptor */
typedef struct {
    trit_irq_handler_t handler;   /**< Handler function (NULL = unregistered) */
    int                enabled;   /**< 1 = enabled, 0 = masked */
    int                count;     /**< Number of times fired */
    const char        *name;      /**< Descriptive name */
} trit_irq_desc_t;

/** IRQ state */
static trit_irq_desc_t irq_table[TRIT_MAX_IRQS];
static int irq_initialized;
static int irq_total_dispatched;

/** Initialize IRQ subsystem */
void trit_irq_init(void) {
    memset(irq_table, 0, sizeof(irq_table));
    irq_initialized = 1;
    irq_total_dispatched = 0;
}

/** Register an IRQ handler */
int trit_irq_register(int irq, trit_irq_handler_t handler, const char *name) {
    if (irq < 0 || irq >= TRIT_MAX_IRQS) return -1;
    if (!handler) return -1;
    irq_table[irq].handler = handler;
    irq_table[irq].enabled = 1;
    irq_table[irq].count = 0;
    irq_table[irq].name = name;
    return 0;
}

/** Unregister an IRQ handler */
int trit_irq_unregister(int irq) {
    if (irq < 0 || irq >= TRIT_MAX_IRQS) return -1;
    irq_table[irq].handler = NULL;
    irq_table[irq].enabled = 0;
    irq_table[irq].name = NULL;
    return 0;
}

/** Enable/disable an IRQ */
int trit_irq_enable(int irq, int enable) {
    if (irq < 0 || irq >= TRIT_MAX_IRQS) return -1;
    irq_table[irq].enabled = enable ? 1 : 0;
    return 0;
}

/** Dispatch an IRQ (called by interrupt controller emulation) */
int trit_irq_dispatch(int irq) {
    if (irq < 0 || irq >= TRIT_MAX_IRQS) return -1;
    if (!irq_table[irq].handler) return -1;
    if (!irq_table[irq].enabled) return -2;  /* masked */
    irq_table[irq].handler(irq);
    irq_table[irq].count++;
    irq_total_dispatched++;
    return 0;
}

/** Query IRQ state */
int trit_irq_get_count(int irq) {
    if (irq < 0 || irq >= TRIT_MAX_IRQS) return -1;
    return irq_table[irq].count;
}

int trit_irq_is_registered(int irq) {
    if (irq < 0 || irq >= TRIT_MAX_IRQS) return 0;
    return irq_table[irq].handler != NULL;
}

int trit_irq_total_dispatched(void) {
    return irq_total_dispatched;
}

/* ---- Timer subsystem -------------------------------------------------- */

/** Trit timer — counts in balanced ternary */
typedef struct {
    int      ticks;           /**< Current tick count */
    int      interval;        /**< Tick interval (ternary modular) */
    int      running;         /**< 1 = running, 0 = stopped */
    trit     phase;           /**< Phase: F→U→T cyclic */
} trit_timer_t;

static trit_timer_t boot_timer;

/** Initialize the arch timer */
void trit_timer_init(int interval) {
    boot_timer.ticks = 0;
    boot_timer.interval = interval;
    boot_timer.running = 1;
    boot_timer.phase = TRIT_FALSE;
}

/** Advance the timer by one tick (cyclic phase: F→U→T→F) */
void trit_timer_tick(void) {
    if (!boot_timer.running) return;
    boot_timer.ticks++;
    /* Cyclic phase: -1 → 0 → +1 → -1 */
    boot_timer.phase = (trit)((boot_timer.phase + 2) % 3 - 1);
}

/** Get current tick count */
int trit_timer_get_ticks(void) {
    return boot_timer.ticks;
}

/** Get current phase */
trit trit_timer_get_phase(void) {
    return boot_timer.phase;
}

/** Stop/start the timer */
void trit_timer_stop(void) { boot_timer.running = 0; }
void trit_timer_start(void) { boot_timer.running = 1; }

/* ---- CPU feature detection -------------------------------------------- */

/** Detected CPU features (bitmask of TRIT_FEAT_*) */
static unsigned int cpu_features;
static int cpu_trit_width;     /* register width in trits */
static int cpu_simd_lanes;     /* SIMD lanes (packed trits) */

/** Detect ternary CPU features.
 *
 * In emulation mode, all software-emulated features are reported.
 * On real ternary hardware, this would probe CPUID-style registers.
 */
void trit_cpu_detect(void) {
    cpu_features = TRIT_FEAT_ALL;      /* emulation has everything */
    cpu_trit_width = 32;               /* trit2_reg32 = 32 trits */
    cpu_simd_lanes = 32;               /* 32 trits packed in uint64_t */
}

/** Report detected features */
unsigned int trit_cpu_features(void) { return cpu_features; }
int trit_cpu_trit_width(void) { return cpu_trit_width; }
int trit_cpu_simd_lanes(void) { return cpu_simd_lanes; }
int trit_cpu_has_feature(unsigned int feat) { return (cpu_features & feat) != 0; }

/** Full arch setup — called from boot */
int trit_arch_setup(void) {
    trit_irq_init();
    trit_timer_init(100);   /* 100-tick default interval */
    trit_cpu_detect();

    /* Validate: all expected features present */
    if (!trit_cpu_has_feature(TRIT_FEAT_SIMD)) return -1;
    if (trit_cpu_trit_width() != 32) return -1;

    return 0;
}
