/**
 * @file syscall.h
 * @brief seT5 Syscall Dispatch — Central Kernel Entry Point
 *
 * Unified syscall interface connecting user-space to kernel subsystems:
 *   - Memory (MMAP)
 *   - Capabilities (SEND, RECV, GRANT, REVOKE)
 *   - Threads (CREATE, YIELD)
 *   - Extended: LOAD_BALANCE, DOT_TRIT
 *
 * Syscall numbers are canonical — defined in set5.h (tools/compiler/include).
 * This module glues the memory, IPC, and scheduler modules together.
 *
 * @see set5.h for syscall number definitions
 * @see ARCHITECTURE.md §8 — Syscall ABI
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_SYSCALL_H
#define SET5_SYSCALL_H

#include "set5/trit.h"
#include "set5/memory.h"
#include "set5/ipc.h"
#include "set5/scheduler.h"
#include "set5/multiradix.h"

#ifdef __cplusplus
extern "C" {
#endif

/* ---- Syscall numbers (canonical — from set5.h) ------------------------ */

#define SYSCALL_EXIT            0
#define SYSCALL_WRITE           1
#define SYSCALL_READ            2
#define SYSCALL_MMAP            3
#define SYSCALL_CAP_SEND        4
#define SYSCALL_CAP_RECV        5
#define SYSCALL_CAP_GRANT       6
#define SYSCALL_CAP_REVOKE      7
#define SYSCALL_THREAD_CREATE   8
#define SYSCALL_THREAD_YIELD    9
/* Extended (seT5-specific) */
#define SYSCALL_LOAD_BALANCE   10
#define SYSCALL_DOT_TRIT       11
#define SYSCALL_FFT_STEP       12
#define SYSCALL_RADIX_CONV     13
#define SYSCALL_COUNT          14

/* ---- Capability table (shared kernel state) --------------------------- */

#define SYSCALL_MAX_CAPS  64

/** Capability entry with ternary validity */
typedef struct {
    int  object_id;    /**< Target kernel object */
    int  rights;       /**< Bitmask: R=1, W=2, G=4 */
    int  badge;        /**< IPC badge for endpoint discrimination */
    trit valid;        /**< T=active, U=pending, F=revoked */
} syscall_cap_t;

/* ---- Kernel State ----------------------------------------------------- */

/** Aggregated kernel state for syscall dispatch */
typedef struct {
    set5_mem_t          mem;        /**< Memory manager */
    ipc_state_t         ipc;        /**< IPC subsystem */
    sched_state_t_state sched;      /**< Scheduler */
    multiradix_state_t  mr;         /**< Multi-radix instruction unit */
    syscall_cap_t       caps[SYSCALL_MAX_CAPS];  /**< Capability table */
    int                 cap_count;  /**< Number of capabilities */
    trit                operand_stack[64]; /**< Operand stack */
    int                 operand_sp;        /**< Stack pointer */
    int                 return_stack[64];  /**< Return stack */
    int                 return_sp;         /**< Return stack pointer */
    int                 stack_overflow;    /**< VULN-59: set 1 on push overflow */
} kernel_state_t;

/* ---- Syscall Result --------------------------------------------------- */

typedef struct {
    int  retval;        /**< Return value (0 = success) */
    trit result_trit;   /**< Ternary result (for trit-returning calls) */
} syscall_result_t;

/* ---- API -------------------------------------------------------------- */

/**
 * @brief Initialise all kernel state (memory, IPC, scheduler, caps).
 * @param ks          Pointer to kernel state.
 * @param num_pages   Number of physical pages to configure.
 */
void kernel_init(kernel_state_t *ks, int num_pages);

/**
 * @brief Dispatch a syscall.
 *
 * Routes the syscall number to the appropriate subsystem, passing
 * arguments and returning results.
 *
 * @param ks     Kernel state.
 * @param sysno  Syscall number (SYSCALL_*).
 * @param arg0   First argument (meaning depends on syscall).
 * @param arg1   Second argument.
 * @return Syscall result with retval and trit result.
 */
syscall_result_t syscall_dispatch(kernel_state_t *ks, int sysno,
                                  int arg0, int arg1);

/**
 * @brief Create a capability in the kernel table.
 *
 * @param ks       Kernel state.
 * @param obj_id   Target object ID.
 * @param rights   Rights bitmask (R=1, W=2, G=4).
 * @param badge    IPC badge.
 * @return Capability index (>= 0), or -1 on failure.
 */
int kernel_cap_create(kernel_state_t *ks, int obj_id, int rights, int badge);

/**
 * @brief Grant a derived capability with narrowed rights.
 *
 * @param ks               Kernel state.
 * @param src_cap_idx      Source capability index.
 * @param requested_rights Rights to request (will be intersected).
 * @return New capability index, or -1 on failure.
 */
int kernel_cap_grant(kernel_state_t *ks, int src_cap_idx,
                     int requested_rights);

/**
 * @brief Revoke a capability (zero rights, mark invalid).
 *
 * @param ks       Kernel state.
 * @param cap_idx  Capability index to revoke.
 * @return 0 on success, -1 on failure.
 */
int kernel_cap_revoke(kernel_state_t *ks, int cap_idx);

/**
 * @brief Check if a capability has a specific right.
 *
 * Conservative check: Unknown validity → deny.
 *
 * @param ks       Kernel state.
 * @param cap_idx  Capability index.
 * @param right    Right to check (CAP_RIGHT_READ, etc.).
 * @return 1 if granted, 0 if denied.
 */
int kernel_cap_check(const kernel_state_t *ks, int cap_idx, int right);

/**
 * @brief Push a trit onto the operand stack.
 * @param ks  Kernel state.
 * @param v   Value to push.
 */
void kernel_push(kernel_state_t *ks, trit v);

/**
 * @brief Pop a trit from the operand stack.
 * @param ks  Kernel state.
 * @return Popped value, or TRIT_UNKNOWN on underflow.
 */
trit kernel_pop(kernel_state_t *ks);

#ifdef __cplusplus
}
#endif

#endif /* SET5_SYSCALL_H */
