/**
 * @file scheduler.c
 * @brief seT5 Trit-Priority Scheduler — Implementation
 *
 * 3-level priority scheduler with balanced ternary priorities:
 *   +1 (True)    = high (real-time, kernel threads)
 *    0 (Unknown) = normal (user-space default)
 *   -1 (False)   = low (background, idle tasks)
 *
 * Selection is O(1) — scan 3 priority buckets, pick first READY.
 * Within each priority level, round-robin via linear scan from
 * last-selected position.
 *
 * @see include/set5/scheduler.h for API documentation
 * @see ARCHITECTURE.md §7 — Scheduling
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/scheduler.h"

/* ==== Initialisation =================================================== */

void sched_init(sched_state_t_state *sched) {
    if (!sched) return;

    sched->thread_count     = 0;
    sched->current_tid      = -1;
    sched->idle_tid         = -1;
    sched->context_switches = 0;
    sched->preemptions      = 0;
    /* VULN-21 is fixed below in sched_pick_next */

    for (int i = 0; i < SCHED_MAX_THREADS; i++) {
        sched->threads[i].tid         = -1;
        sched->threads[i].priority    = TRIT_UNKNOWN;
        sched->threads[i].state       = SCHED_DEAD;
        sched->threads[i].entry_addr  = 0;
        sched->threads[i].blocked_on  = -1;
        sched->threads[i].time_slice  = 3;   /* 3 trits = 1 tryte quantum */
        sched->threads[i].cpu_affinity = -1; /* any CPU */
    }
}

/* ==== Thread Creation / Destruction ==================================== */

int sched_create(sched_state_t_state *sched, int entry_addr, trit priority) {
    if (!sched) return -1;
    if (sched->thread_count >= SCHED_MAX_THREADS) return -1;

    /* Validate priority is valid trit */
    if (priority < TRIT_FALSE || priority > TRIT_TRUE)
        priority = TRIT_UNKNOWN;  /* default to normal */

    int tid = sched->thread_count++;
    sched_tcb_t *tcb = &sched->threads[tid];
    tcb->tid          = tid;
    tcb->priority     = priority;
    tcb->state        = SCHED_READY;
    tcb->entry_addr   = entry_addr;
    tcb->blocked_on   = -1;
    tcb->time_slice   = 3;
    tcb->cpu_affinity = -1;
    return tid;
}

int sched_destroy(sched_state_t_state *sched, int tid) {
    if (!sched) return -1;
    if (tid < 0 || tid >= sched->thread_count) return -1;

    sched_tcb_t *tcb = &sched->threads[tid];
    if (tcb->state == SCHED_DEAD) return -1;  /* already dead */

    tcb->state      = SCHED_DEAD;
    tcb->blocked_on = -1;

    /* If we killed the current thread, need to reschedule */
    if (sched->current_tid == tid)
        sched->current_tid = -1;

    return 0;
}

/* ==== Scheduling ======================================================= */

int sched_pick_next(sched_state_t_state *sched) {
    if (!sched) return -1;

    /*
     * Priority scan: high (+1) → normal (0) → low (-1)
     * VULN-21 fix: within each priority level, start scan from
     * (current_tid + 1) to ensure round-robin fairness.
     *
     * With only 3 priority levels and bounded thread count,
     * this is effectively O(1) for system-level scheduling.
     */
    trit levels[3] = { TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE };
    int start = (sched->current_tid >= 0) ? sched->current_tid + 1 : 0;

    for (int lvl = 0; lvl < 3; lvl++) {
        for (int j = 0; j < sched->thread_count; j++) {
            int i = (start + j) % sched->thread_count;
            sched_tcb_t *tcb = &sched->threads[i];
            if (tcb->state == SCHED_READY && tcb->priority == levels[lvl]) {
                return tcb->tid;
            }
        }
    }

    return -1;  /* no runnable threads — idle */
}

int sched_yield(sched_state_t_state *sched) {
    if (!sched) return -1;

    /* Current thread → READY */
    if (sched->current_tid >= 0) {
        sched_tcb_t *cur = &sched->threads[sched->current_tid];
        if (cur->state == SCHED_RUNNING)
            cur->state = SCHED_READY;
    }

    /* Pick next */
    int next = sched_pick_next(sched);

    if (next >= 0 && next != sched->current_tid) {
        sched->context_switches++;
    }

    sched->current_tid = next;
    if (next >= 0) {
        sched->threads[next].state = SCHED_RUNNING;
    }

    return next;
}

/* ==== Block / Unblock ================================================== */

int sched_block(sched_state_t_state *sched, int tid, int blocked_on) {
    if (!sched) return -1;
    if (tid < 0 || tid >= sched->thread_count) return -1;

    sched_tcb_t *tcb = &sched->threads[tid];
    if (tcb->state == SCHED_DEAD) return -1;

    tcb->state      = SCHED_BLOCKED;
    tcb->blocked_on = blocked_on;

    /* If blocking current thread, need to pick a new one */
    if (sched->current_tid == tid) {
        sched->current_tid = -1;
    }

    return 0;
}

int sched_unblock(sched_state_t_state *sched, int tid) {
    if (!sched) return -1;
    if (tid < 0 || tid >= sched->thread_count) return -1;

    sched_tcb_t *tcb = &sched->threads[tid];
    if (tcb->state != SCHED_BLOCKED) return -1;

    tcb->state      = SCHED_READY;
    tcb->blocked_on = -1;
    return 0;
}

/* ==== Priority ========================================================= */

int sched_set_priority(sched_state_t_state *sched, int tid, trit priority) {
    if (!sched) return -1;
    if (tid < 0 || tid >= sched->thread_count) return -1;
    if (priority < TRIT_FALSE || priority > TRIT_TRUE) return -1;

    sched->threads[tid].priority = priority;
    return 0;
}

/* ==== Statistics ======================================================= */

void sched_stats(const sched_state_t_state *sched,
                 int *total_threads, int *ready_count,
                 int *blocked_count, int *context_switches) {
    if (!sched) return;

    int ready = 0, blocked = 0;
    for (int i = 0; i < sched->thread_count; i++) {
        switch (sched->threads[i].state) {
        case SCHED_READY:   ready++;   break;
        case SCHED_BLOCKED: blocked++; break;
        default: break;
        }
    }

    if (total_threads)    *total_threads    = sched->thread_count;
    if (ready_count)      *ready_count      = ready;
    if (blocked_count)    *blocked_count    = blocked;
    if (context_switches) *context_switches = sched->context_switches;
}
