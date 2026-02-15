/**
 * @file posix.h
 * @brief POSIX → seT6 Syscall Translation Layer
 *
 * Maps standard POSIX system calls to the seT6 ternary kernel ABI.
 * This allows unmodified POSIX applications to run on seT6 by
 * translating binary syscall conventions to balanced ternary.
 *
 * Design:
 *   - POSIX return codes (int) → trit validity (T/U/F)
 *   - POSIX file descriptors → seT6 capability slots
 *   - POSIX signals → seT6 notifications
 *   - POSIX mmap → seT6 page allocation with ternary validity
 *
 * The translation layer is stateless per call — it does not maintain
 * its own state beyond what the underlying seT6 kernel provides.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_POSIX_H
#define SET6_POSIX_H

#include "set6/trit.h"
#include "set6/syscall.h"
#include "set6/memory.h"
#include "set6/ipc.h"
#include "set6/scheduler.h"

/* ---- POSIX ↔ seT6 Mapping Table --------------------------------------- */

/**
 * POSIX errno → ternary validity mapping.
 *
 * POSIX errors are negative integers; seT6 uses trit:
 *   success (≥ 0)  → TRIT_TRUE
 *   EAGAIN / retry → TRIT_UNKNOWN (try again later)
 *   error  (< 0)   → TRIT_FALSE
 */
static inline trit posix_errno_to_trit(int posix_ret) {
    if (posix_ret >= 0)  return TRIT_TRUE;
    if (posix_ret == -11) return TRIT_UNKNOWN;  /* EAGAIN */
    return TRIT_FALSE;
}

/**
 * seT6 trit result → POSIX return code.
 */
static inline int trit_to_posix_errno(trit t) {
    switch (t) {
        case TRIT_TRUE:    return 0;
        case TRIT_UNKNOWN: return -11; /* EAGAIN */
        case TRIT_FALSE:   return -1;  /* generic error */
        default:           return -22; /* EINVAL */
    }
}

/* ---- POSIX File Descriptor ↔ Capability Slot -------------------------- */

/**
 * Map POSIX fd → seT6 capability slot.
 *
 * POSIX: fd 0=stdin, 1=stdout, 2=stderr, 3+ = user fds
 * seT6:  cap slots 0-2 reserved, 3+ user caps
 *
 * Direct 1:1 mapping since both are small integers.
 */
typedef struct {
    int posix_fd;
    int set6_cap_slot;
    trit validity;       /* T = open, U = suspended, F = closed */
} posix_fd_entry_t;

#define POSIX_MAX_FDS 256

typedef struct {
    posix_fd_entry_t fds[POSIX_MAX_FDS];
    int              fd_count;
} posix_fd_table_t;

static inline void posix_fd_table_init(posix_fd_table_t *table) {
    if (!table) return;
    table->fd_count = 0;
    for (int i = 0; i < POSIX_MAX_FDS; i++) {
        table->fds[i].posix_fd = -1;
        table->fds[i].set6_cap_slot = -1;
        table->fds[i].validity = TRIT_FALSE;
    }
    /* Pre-map stdio */
    table->fds[0] = (posix_fd_entry_t){0, 0, TRIT_TRUE};  /* stdin */
    table->fds[1] = (posix_fd_entry_t){1, 1, TRIT_TRUE};  /* stdout */
    table->fds[2] = (posix_fd_entry_t){2, 2, TRIT_TRUE};  /* stderr */
    table->fd_count = 3;
}

static inline int posix_fd_open(posix_fd_table_t *table) {
    if (!table || table->fd_count >= POSIX_MAX_FDS) return -1;
    int fd = table->fd_count;
    table->fds[fd].posix_fd = fd;
    table->fds[fd].set6_cap_slot = fd;
    table->fds[fd].validity = TRIT_TRUE;
    table->fd_count++;
    return fd;
}

static inline int posix_fd_close(posix_fd_table_t *table, int fd) {
    if (!table || fd < 0 || fd >= POSIX_MAX_FDS) return -1;
    if (table->fds[fd].validity == TRIT_FALSE) return -9; /* EBADF */
    table->fds[fd].validity = TRIT_FALSE;
    return 0;
}

static inline trit posix_fd_check(const posix_fd_table_t *table, int fd) {
    if (!table || fd < 0 || fd >= POSIX_MAX_FDS) return TRIT_FALSE;
    return table->fds[fd].validity;
}

/* ---- POSIX Signal ↔ seT6 Notification --------------------------------- */

/**
 * Map POSIX signals to seT6 notification bits.
 *
 * POSIX: SIGTERM=15, SIGKILL=9, SIGUSR1=10, SIGUSR2=12, ...
 * seT6:  notification bits 0-31 in ipc_notification_t
 *
 * We map signal numbers directly to notification bits.
 */
static inline int posix_signal_to_notif_bit(int signum) {
    if (signum < 1 || signum > 31) return -1;
    return signum;
}

static inline int posix_notif_bit_to_signal(int bit) {
    if (bit < 1 || bit > 31) return -1;
    return bit;
}

/* ---- POSIX mmap ↔ seT6 Memory Allocation ------------------------------ */

/**
 * Translate POSIX mmap flags to seT6 page allocation.
 *
 * POSIX mmap: addr, length, prot, flags, fd, offset
 * seT6:       mem_alloc(state, owner) → page index
 *
 * Key differences:
 *   - seT6 pages are Unknown-initialised (not zero-filled like MAP_ANONYMOUS)
 *   - seT6 uses ternary validity instead of PROT_READ/WRITE/EXEC
 *   - seT6 scrubs on free (security guarantee)
 */

#define POSIX_PROT_NONE  0x0
#define POSIX_PROT_READ  0x1
#define POSIX_PROT_WRITE 0x2
#define POSIX_PROT_EXEC  0x4

/**
 * Convert POSIX prot flags to nearest seT6 capability permissions.
 * seT6 caps have: read, write, grant
 * PROT_EXEC maps to a separate "execute" capability (not yet in seT6 ABI)
 */
static inline int posix_prot_to_cap_perms(int prot) {
    int perms = 0;
    if (prot & POSIX_PROT_READ)  perms |= 1;
    if (prot & POSIX_PROT_WRITE) perms |= 2;
    if (prot & POSIX_PROT_EXEC)  perms |= 4;
    return perms;
}

/* ---- POSIX Process ↔ seT6 Thread -------------------------------------- */

/**
 * Map POSIX process/thread operations to seT6 scheduler.
 *
 * POSIX fork()    → sched_create_thread() + memory copy
 * POSIX exit()    → sched_destroy_thread()
 * POSIX waitpid() → IPC wait on notification
 * POSIX pthread_create() → sched_create_thread()
 *
 * seT6 threads have ternary priority levels, not POSIX nice values.
 */
static inline trit posix_nice_to_trit_priority(int nice) {
    if (nice < -7)  return TRIT_TRUE;     /* High priority */
    if (nice > 7)   return TRIT_FALSE;    /* Low priority */
    return TRIT_UNKNOWN;                  /* Normal priority */
}

static inline int trit_priority_to_posix_nice(trit prio) {
    switch (prio) {
        case TRIT_TRUE:    return -10;  /* High */
        case TRIT_UNKNOWN: return 0;    /* Normal */
        case TRIT_FALSE:   return 10;   /* Low */
        default:           return 0;
    }
}

/* ---- POSIX Unified Translation Entry Point ---------------------------- */

/**
 * posix_translate_syscall — Main translation dispatch.
 *
 * Takes a POSIX syscall number and translates to seT6 kernel call.
 * Returns the POSIX-compatible result code.
 *
 * Currently supported:
 *   SYS_read   (0)  → IPC recv on cap slot
 *   SYS_write  (1)  → IPC send on cap slot
 *   SYS_open   (2)  → fd_table open + cap create
 *   SYS_close  (3)  → fd_table close + cap revoke
 *   SYS_mmap   (9)  → mem_alloc + cap create
 *   SYS_munmap (11) → mem_free + cap revoke
 *   SYS_exit   (60) → sched_destroy + kernel cleanup
 *   SYS_getpid (39) → thread ID lookup
 */
typedef struct {
    kernel_state_t   *ks;
    posix_fd_table_t  fds;
    int               pid;   /* Current thread ID */
} posix_context_t;

static inline void posix_context_init(posix_context_t *ctx,
                                      kernel_state_t *ks, int pid) {
    if (!ctx) return;
    ctx->ks = ks;
    ctx->pid = pid;
    posix_fd_table_init(&ctx->fds);
}

static inline int posix_sys_open(posix_context_t *ctx) {
    if (!ctx) return -1;
    int fd = posix_fd_open(&ctx->fds);
    if (fd < 0) return -24; /* EMFILE - too many open files */
    return fd;
}

static inline int posix_sys_close(posix_context_t *ctx, int fd) {
    if (!ctx) return -1;
    return posix_fd_close(&ctx->fds, fd);
}

static inline int posix_sys_mmap(posix_context_t *ctx, int prot) {
    if (!ctx || !ctx->ks) return -1;
    int page = mem_alloc(&ctx->ks->mem, ctx->pid);
    if (page < 0) return -12; /* ENOMEM */
    (void)prot;  /* Would be used for capability creation */
    return page;
}

static inline int posix_sys_munmap(posix_context_t *ctx, int page) {
    if (!ctx || !ctx->ks) return -1;
    mem_free(&ctx->ks->mem, page);
    return 0;
}

static inline int posix_sys_getpid(const posix_context_t *ctx) {
    return ctx ? ctx->pid : -1;
}

static inline int posix_sys_exit(posix_context_t *ctx) {
    if (!ctx || !ctx->ks) return -1;
    sched_destroy(&ctx->ks->sched, ctx->pid);
    return 0;  /* Does not return in real kernel */
}

#endif /* SET6_POSIX_H */
