/**
 * @file wcet.h
 * @brief seT6 WCET (Worst-Case Execution Time) Analysis Framework
 *
 * Provides instrumentation and analysis for bounding the execution
 * time of ternary kernel operations. This is critical for seL4-style
 * real-time guarantees.
 *
 * Ternary branching introduces a third path at each decision point,
 * which can affect WCET bounds. The key insight is that Kleene logic
 * has bounded complexity:
 *
 *   - trit_and / trit_or: O(1) — min/max on 3-element set
 *   - trit_not: O(1) — negation
 *   - DOT_TRIT: O(n) where n = register width (32)
 *   - FFT_STEP: O(n/3) butterfly groups
 *   - RADIX_CONV: O(log₃(value))
 *   - Syscall dispatch: O(1) switch + subsystem cost
 *
 * For the memory manager, worst case is a full page table scan: O(MAX_PAGES).
 * For IPC, worst case is endpoint state transition: O(1).
 * For scheduler, worst case is a full priority scan: O(MAX_THREADS).
 *
 * WCET budgets (in abstract cycles, calibrated per-platform):
 *
 *   | Operation        | Budget (cycles) | Notes                     |
 *   |------------------|-----------------|---------------------------|
 *   | Syscall entry    | 20              | Dispatch + cap check      |
 *   | mem_alloc        | 300             | Linear scan, 256 max      |
 *   | mem_free         | 800             | Scan + scrub (729 trits)  |
 *   | ipc_send/recv    | 50              | State machine + copy      |
 *   | sched_yield      | 200             | 3-level priority scan     |
 *   | dot_trit         | 100             | 32-trit SIMD path         |
 *   | fft_step         | 120             | 10 butterfly groups       |
 *   | cap_check        | 10              | Array lookup              |
 *
 * @see ARCHITECTURE.md §9 — WCET Framework
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_WCET_H
#define SET6_WCET_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ---- WCET Budget Constants -------------------------------------------- */

#define WCET_SYSCALL_ENTRY       20
#define WCET_MEM_ALLOC          300
#define WCET_MEM_FREE           800
#define WCET_MEM_READ            10
#define WCET_MEM_WRITE           10
#define WCET_IPC_SEND            50
#define WCET_IPC_RECV            50
#define WCET_IPC_SIGNAL          20
#define WCET_IPC_WAIT            20
#define WCET_SCHED_YIELD        200
#define WCET_SCHED_CREATE        30
#define WCET_CAP_CHECK           10
#define WCET_CAP_GRANT           20
#define WCET_CAP_REVOKE          15
#define WCET_DOT_TRIT           100
#define WCET_FFT_STEP           120
#define WCET_RADIX_CONV          80
#define WCET_TRIT_LB_SNAPSHOT    30
#define WCET_KERNEL_PUSH          5
#define WCET_KERNEL_POP           5

/* ---- WCET Instrumentation -------------------------------------------- */

/** Maximum number of instrumentation points */
#define WCET_MAX_PROBES  64

/** A single WCET measurement point */
typedef struct {
    const char *label;          /**< Human-readable probe name */
    uint64_t    budget_cycles;  /**< WCET budget in abstract cycles */
    uint64_t    observed_max;   /**< Maximum observed cycles */
    uint64_t    observed_sum;   /**< Sum for average calculation */
    uint32_t    invocation_count; /**< Number of invocations */
    int         violation_count;  /**< Times budget was exceeded */
} wcet_probe_t;

/** WCET analysis state */
typedef struct {
    wcet_probe_t probes[WCET_MAX_PROBES]; /**< Instrumentation array */
    int          probe_count;             /**< Number of active probes */
    uint64_t     global_tick;             /**< Monotonic tick counter */
    int          total_violations;        /**< Total budget violations */
} wcet_state_t;

/**
 * @brief Initialise the WCET analysis state.
 * @param state  WCET state to initialise.
 */
static inline void wcet_init(wcet_state_t *state) {
    if (!state) return;
    for (int i = 0; i < WCET_MAX_PROBES; i++) {
        state->probes[i].label     = "";
        state->probes[i].budget_cycles = 0;
        state->probes[i].observed_max  = 0;
        state->probes[i].observed_sum  = 0;
        state->probes[i].invocation_count = 0;
        state->probes[i].violation_count  = 0;
    }
    state->probe_count      = 0;
    state->global_tick       = 0;
    state->total_violations  = 0;
}

/**
 * @brief Register a new WCET probe.
 *
 * @param state   WCET state.
 * @param label   Probe name (string must remain valid).
 * @param budget  WCET budget in abstract cycles.
 * @return        Probe index, or -1 if table full.
 */
static inline int wcet_register(wcet_state_t *state, const char *label,
                                uint64_t budget) {
    if (!state || state->probe_count >= WCET_MAX_PROBES) return -1;
    int idx = state->probe_count++;
    state->probes[idx].label          = label;
    state->probes[idx].budget_cycles  = budget;
    state->probes[idx].observed_max   = 0;
    state->probes[idx].observed_sum   = 0;
    state->probes[idx].invocation_count = 0;
    state->probes[idx].violation_count  = 0;
    return idx;
}

/**
 * @brief Record an observation for a WCET probe.
 *
 * Updates the maximum, sum, and invocation count. If the observed
 * cycles exceed the budget, increments the violation counter.
 *
 * @param state   WCET state.
 * @param probe   Probe index.
 * @param cycles  Observed cycle count for this invocation.
 */
static inline void wcet_observe(wcet_state_t *state, int probe,
                                uint64_t cycles) {
    if (!state || probe < 0 || probe >= state->probe_count) return;

    wcet_probe_t *p = &state->probes[probe];
    p->invocation_count++;
    p->observed_sum += cycles;

    if (cycles > p->observed_max) {
        p->observed_max = cycles;
    }

    if (cycles > p->budget_cycles) {
        p->violation_count++;
        state->total_violations++;
    }

    state->global_tick += cycles;
}

/**
 * @brief Check if any WCET budget has been violated.
 * @param state  WCET state.
 * @return       Number of total violations (0 = clean).
 */
static inline int wcet_check(const wcet_state_t *state) {
    if (!state) return 0;
    return state->total_violations;
}

/**
 * @brief Get the utilization ratio for a probe (observed_max / budget).
 *
 * Returns percentage 0-100+. Values >100 indicate budget violation.
 *
 * @param state  WCET state.
 * @param probe  Probe index.
 * @return       Utilization as percentage (0 if no observations).
 */
static inline int wcet_utilization_pct(const wcet_state_t *state, int probe) {
    if (!state || probe < 0 || probe >= state->probe_count) return 0;
    const wcet_probe_t *p = &state->probes[probe];
    if (p->budget_cycles == 0) return 0;
    return (int)((p->observed_max * 100) / p->budget_cycles);
}

/**
 * @brief Get average cycles for a probe.
 * @param state  WCET state.
 * @param probe  Probe index.
 * @return       Average cycles per invocation.
 */
static inline uint64_t wcet_average(const wcet_state_t *state, int probe) {
    if (!state || probe < 0 || probe >= state->probe_count) return 0;
    const wcet_probe_t *p = &state->probes[probe];
    if (p->invocation_count == 0) return 0;
    return p->observed_sum / p->invocation_count;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_WCET_H */
