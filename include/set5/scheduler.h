/**
 * @file scheduler.h
 * @brief seT5 Trit-Priority Scheduler
 *
 * Priority-based preemptive scheduler using balanced ternary priorities:
 *   - True (+1):    high priority (real-time / kernel)
 *   - Unknown (0):  normal priority (user-space default)
 *   - False (-1):   low priority (background / idle)
 *
 * Features:
 *   - 3-level priority with round-robin within each level
 *   - Thread states: Ready, Running, Blocked, Dead
 *   - Capability-guarded thread creation (requires CAP_RIGHT_WRITE)
 *   - Context switch via yield / preemption
 *   - IPC integration: block/unblock threads on endpoint events
 *
 * Design note: With 3 priority levels, the scheduler run queue is
 * trivially O(1) — scan 3 buckets, pick first non-empty.  This
 * matches seL4's fixed-priority scheduling but exploits ternary
 * ordering for natural priority representation.
 *
 * @see ARCHITECTURE.md §7 — Scheduling
 * @see init.c for bootstrap usage
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SCHEDULER_H
#define SET5_SCHEDULER_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Configuration ---------------------------------------------------- */

/** Maximum threads in the system */
#define SCHED_MAX_THREADS  64

/* ---- Thread States ---------------------------------------------------- */

typedef enum {
    SCHED_READY,       /**< Runnable, in a priority queue */
    SCHED_RUNNING,     /**< Currently executing */
    SCHED_BLOCKED,     /**< Waiting on IPC/notification/timer */
    SCHED_DEAD         /**< Terminated or not yet created */
} sched_state_t;

/* ---- Thread Control Block --------------------------------------------- */

typedef struct {
    int            tid;            /**< Thread ID (0-based) */
    trit           priority;       /**< -1=low, 0=normal, +1=high */
    sched_state_t  state;          /**< Current state */
    int            entry_addr;     /**< Entry point (instruction address) */
    int            blocked_on;     /**< Endpoint/notification idx (-1=none) */
    int            time_slice;     /**< Remaining time slice (trits) */
    int            cpu_affinity;   /**< CPU affinity (-1=any) */
} sched_tcb_t;

/* ---- Scheduler State -------------------------------------------------- */

typedef struct {
    sched_tcb_t threads[SCHED_MAX_THREADS];
    int         thread_count;      /**< Total created threads */
    int         current_tid;       /**< Currently running thread (-1=idle) */
    int         idle_tid;          /**< Dedicated idle thread (-1=none) */
    int         context_switches;  /**< Total context switch count */
    int         preemptions;       /**< Preemption count */
} sched_state_t_state;

/* ---- API -------------------------------------------------------------- */

/**
 * @brief Initialise the scheduler.
 * @param sched  Pointer to scheduler state.
 */
void sched_init(sched_state_t_state *sched);

/**
 * @brief Create a new thread.
 *
 * @param sched      Scheduler state.
 * @param entry_addr Entry point address.
 * @param priority   Trit priority: +1=high, 0=normal, -1=low.
 * @return Thread ID (>= 0) on success, -1 if at capacity.
 */
int sched_create(sched_state_t_state *sched, int entry_addr, trit priority);

/**
 * @brief Destroy a thread (mark as Dead).
 *
 * @param sched  Scheduler state.
 * @param tid    Thread ID to destroy.
 * @return 0 on success, -1 if invalid.
 */
int sched_destroy(sched_state_t_state *sched, int tid);

/**
 * @brief Pick the next runnable thread (highest priority, round-robin).
 *
 * Scans priority buckets from high (+1) to low (-1), returns first
 * READY thread found.  O(1) with 3 fixed priority levels.
 *
 * @param sched  Scheduler state.
 * @return Thread ID of next thread, or -1 if no runnable threads.
 */
int sched_pick_next(sched_state_t_state *sched);

/**
 * @brief Yield: current thread → READY, pick and switch to next.
 *
 * @param sched  Scheduler state.
 * @return New current thread ID, or -1 if idle.
 */
int sched_yield(sched_state_t_state *sched);

/**
 * @brief Block a thread (e.g., waiting on IPC).
 *
 * @param sched      Scheduler state.
 * @param tid        Thread to block.
 * @param blocked_on Object index blocking on (-1 for generic block).
 * @return 0 on success, -1 if invalid.
 */
int sched_block(sched_state_t_state *sched, int tid, int blocked_on);

/**
 * @brief Unblock a thread (e.g., IPC completed).
 *
 * @param sched  Scheduler state.
 * @param tid    Thread to unblock.
 * @return 0 on success, -1 if invalid or not blocked.
 */
int sched_unblock(sched_state_t_state *sched, int tid);

/**
 * @brief Set thread priority.
 *
 * @param sched     Scheduler state.
 * @param tid       Thread ID.
 * @param priority  New trit priority.
 * @return 0 on success, -1 if invalid.
 */
int sched_set_priority(sched_state_t_state *sched, int tid, trit priority);

/**
 * @brief Get scheduling statistics.
 *
 * @param sched                  Scheduler state.
 * @param[out] total_threads     Total thread count.
 * @param[out] ready_count       Number of READY threads.
 * @param[out] blocked_count     Number of BLOCKED threads.
 * @param[out] context_switches  Total context switch count.
 */
void sched_stats(const sched_state_t_state *sched,
                 int *total_threads, int *ready_count,
                 int *blocked_count, int *context_switches);

#ifdef __cplusplus
}
#endif

#endif /* SET5_SCHEDULER_H */
