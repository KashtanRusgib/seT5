/**
 * @file syscall.c
 * @brief seT6 Syscall Dispatch — Unified Kernel Entry Point
 *
 * Central dispatch that routes syscall numbers to the appropriate
 * kernel subsystem (memory, IPC, scheduler, capabilities).
 *
 * All syscall numbers match the canonical ABI in set6.h.
 * The kernel state aggregates all subsystem states into a single
 * structure for straightforward capability checking and dispatch.
 *
 * @see include/set6/syscall.h for API documentation
 * @see ARCHITECTURE.md §8 — Syscall ABI
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set6/syscall.h"
#include "set6/trit_cast.h"
#include <string.h>

/* ==== Kernel Init ====================================================== */

void kernel_init(kernel_state_t *ks, int num_pages) {
    if (!ks) return;

    /* Memory manager */
    mem_init(&ks->mem, num_pages);

    /* IPC subsystem */
    ipc_init(&ks->ipc);

    /* Scheduler */
    sched_init(&ks->sched);

    /* Multi-radix instruction unit */
    multiradix_init(&ks->mr);

    /* Capability table */
    ks->cap_count = 0;
    for (int i = 0; i < SYSCALL_MAX_CAPS; i++) {
        ks->caps[i].object_id = -1;
        ks->caps[i].rights    = 0;
        ks->caps[i].badge     = 0;
        ks->caps[i].valid     = TRIT_FALSE;
    }

    /* Stacks */
    ks->operand_sp = 0;
    ks->return_sp  = 0;
    for (int i = 0; i < 64; i++) {
        ks->operand_stack[i] = TRIT_UNKNOWN;
        ks->return_stack[i]  = 0;
    }
}

/* ==== Capability Table ================================================= */

int kernel_cap_create(kernel_state_t *ks, int obj_id, int rights, int badge) {
    if (!ks || ks->cap_count >= SYSCALL_MAX_CAPS) return -1;

    int idx = ks->cap_count++;
    ks->caps[idx].object_id = obj_id;
    ks->caps[idx].rights    = rights & 7;  /* mask to R|W|G */
    ks->caps[idx].badge     = badge;
    ks->caps[idx].valid     = TRIT_TRUE;
    return idx;
}

int kernel_cap_grant(kernel_state_t *ks, int src_cap_idx,
                     int requested_rights) {
    if (!ks) return -1;
    if (src_cap_idx < 0 || src_cap_idx >= ks->cap_count) return -1;

    syscall_cap_t *src = &ks->caps[src_cap_idx];
    if (src->valid != TRIT_TRUE) return -1;
    if (!(src->rights & 4)) return -1;  /* need GRANT right on source */

    /* Monotonicity: rights can only narrow */
    int narrowed = src->rights & requested_rights;
    return kernel_cap_create(ks, src->object_id, narrowed, src->badge);
}

int kernel_cap_revoke(kernel_state_t *ks, int cap_idx) {
    if (!ks) return -1;
    if (cap_idx < 0 || cap_idx >= ks->cap_count) return -1;

    ks->caps[cap_idx].rights = 0;
    ks->caps[cap_idx].badge  = 0;
    ks->caps[cap_idx].valid  = TRIT_FALSE;
    return 0;
}

int kernel_cap_check(const kernel_state_t *ks, int cap_idx, int right) {
    if (!ks) return 0;
    if (cap_idx < 0 || cap_idx >= ks->cap_count) return 0;

    const syscall_cap_t *cap = &ks->caps[cap_idx];
    /* Conservative: Unknown validity → deny */
    if (cap->valid != TRIT_TRUE) return 0;
    return (cap->rights & right) != 0;
}

/* ==== Stack Operations ================================================= */

void kernel_push(kernel_state_t *ks, trit v) {
    if (!ks) return;
    if (ks->operand_sp < 64)
        ks->operand_stack[ks->operand_sp++] = v;
}

trit kernel_pop(kernel_state_t *ks) {
    if (!ks || ks->operand_sp <= 0) return TRIT_UNKNOWN;
    return ks->operand_stack[--ks->operand_sp];
}

/* ==== Syscall Dispatch ================================================= */

syscall_result_t syscall_dispatch(kernel_state_t *ks, int sysno,
                                  int arg0, int arg1) {
    syscall_result_t res = { .retval = -1, .result_trit = TRIT_UNKNOWN };
    if (!ks) return res;

    switch (sysno) {

    case SYSCALL_EXIT:
        /* Destroy current thread */
        if (ks->sched.current_tid >= 0) {
            sched_destroy(&ks->sched, ks->sched.current_tid);
        }
        res.retval      = 0;
        res.result_trit = TRIT_FALSE;  /* terminated */
        break;

    case SYSCALL_WRITE:
        /* arg0=fd, arg1=len — stub: succeed if valid fd */
        res.retval      = (arg0 >= 0) ? arg1 : -1;
        res.result_trit = trit_from_int(res.retval >= 0 ? 1 : -1);
        break;

    case SYSCALL_READ:
        /* arg0=fd, arg1=len — stub: return 0 bytes */
        res.retval      = 0;
        res.result_trit = TRIT_UNKNOWN;
        break;

    case SYSCALL_MMAP: {
        /* Allocate a page, assign to current thread */
        int owner = ks->sched.current_tid;
        int pg = mem_alloc(&ks->mem, owner >= 0 ? owner : -1);
        res.retval      = pg;
        res.result_trit = trit_from_int(pg >= 0 ? 1 : -1);
        kernel_push(ks, res.result_trit);
        break;
    }

    case SYSCALL_CAP_SEND: {
        /* arg0=ep_idx, arg1=badge */
        ipc_msg_t msg;
        trit payload = kernel_pop(ks);
        ipc_msg_build(&msg, &payload, 1, arg1, ks->sched.current_tid);
        int r = ipc_send(&ks->ipc, arg0, &msg, ks->sched.current_tid);
        if (r == 1) {
            /* Sender blocks */
            sched_block(&ks->sched, ks->sched.current_tid, arg0);
        }
        res.retval      = r;
        res.result_trit = trit_from_int(r == 0 ? 1 : 0);
        break;
    }

    case SYSCALL_CAP_RECV: {
        /* arg0=ep_idx */
        ipc_msg_t msg;
        int r = ipc_recv(&ks->ipc, arg0, &msg, ks->sched.current_tid);
        if (r == 0) {
            /* Got a message — push first word */
            kernel_push(ks, msg.words[0]);
            res.retval = msg.sender_badge;
        } else if (r == 1) {
            /* Receiver blocks */
            sched_block(&ks->sched, ks->sched.current_tid, arg0);
            res.retval = 0;
        } else {
            res.retval = -1;
        }
        res.result_trit = trit_from_int(r == 0 ? 1 : 0);
        break;
    }

    case SYSCALL_CAP_GRANT: {
        /* arg0=src_cap_idx, arg1=requested_rights */
        int new_cap = kernel_cap_grant(ks, arg0, arg1);
        res.retval      = new_cap;
        res.result_trit = trit_from_int(new_cap >= 0 ? 1 : -1);
        break;
    }

    case SYSCALL_CAP_REVOKE:
        /* arg0=cap_idx */
        res.retval      = kernel_cap_revoke(ks, arg0);
        res.result_trit = trit_from_int(res.retval == 0 ? 1 : -1);
        break;

    case SYSCALL_THREAD_CREATE: {
        /* arg0=entry_addr, arg1=priority */
        trit prio = trit_from_int(arg1);
        int tid = sched_create(&ks->sched, arg0, prio);
        res.retval      = tid;
        res.result_trit = trit_from_int(tid >= 0 ? 1 : -1);
        break;
    }

    case SYSCALL_THREAD_YIELD: {
        int next = sched_yield(&ks->sched);
        res.retval      = next;
        res.result_trit = trit_from_int(next >= 0 ? 1 : 0);
        break;
    }

    case SYSCALL_LOAD_BALANCE:
        /* G300-inspired multi-radix load balance hook */
        /* arg0=priority, arg1=affinity */
        if (ks->sched.current_tid >= 0) {
            sched_set_priority(&ks->sched, ks->sched.current_tid,
                               trit_from_int(arg0));
            ks->sched.threads[ks->sched.current_tid].cpu_affinity = arg1;
        }
        res.retval      = 0;
        res.result_trit = TRIT_TRUE;
        break;

    case SYSCALL_DOT_TRIT: {
        /* Ternary dot product — arg0=reg_a, arg1=reg_b */
        int dp = dot_trit(&ks->mr, arg0, arg1);
        res.retval      = dp;
        res.result_trit = trit_from_int(dp > 0 ? 1 : (dp < 0 ? -1 : 0));
        break;
    }

    case SYSCALL_FFT_STEP: {
        /* Radix-3 butterfly — arg0=reg_in, arg1=reg_out (stride=1) */
        int r = fft_step(&ks->mr, arg0, arg1, 1);
        res.retval      = r;
        res.result_trit = trit_from_int(r >= 0 ? 1 : -1);
        break;
    }

    case SYSCALL_RADIX_CONV: {
        /* arg0=reg, arg1=binary_value — convert to balanced ternary */
        int nz = radix_conv_to_ternary(&ks->mr, arg0, arg1);
        res.retval      = nz;
        res.result_trit = trit_from_int(nz >= 0 ? 1 : -1);
        break;
    }

    default:
        /* Unknown syscall — return Unknown (safe) */
        res.retval      = -1;
        res.result_trit = TRIT_UNKNOWN;
        break;
    }

    return res;
}
