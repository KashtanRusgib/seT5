/*
 * set5.h - seT5 Ternary Microkernel Syscall Interface (TASK-016)
 *
 * Defines the syscall ABI for the seT5 microkernel — a capability-based
 * ternary operating system inspired by seL4. All syscalls use the VM's
 * OP_SYSCALL opcode with the syscall number on the stack.
 *
 * Syscall convention:
 *   PUSH <args...>   (right-to-left)
 *   PUSH <syscall_no>
 *   SYSCALL
 *   -> result on stack
 */

#ifndef SET5_H
#define SET5_H

/* ---- Syscall numbers ---- */
#define SYS_EXIT       0   /* t_exit: terminate process */
#define SYS_WRITE      1   /* t_write(fd, addr, len) -> bytes_written */
#define SYS_READ       2   /* t_read(fd, addr, len) -> bytes_read */
#define SYS_MMAP       3   /* t_mmap(size) -> base_addr */
#define SYS_CAP_SEND   4   /* t_cap_send(cap, msg) -> 0 on success */
#define SYS_CAP_RECV   5   /* t_cap_recv(cap) -> msg */
#define SYS_CAP_GRANT  6   /* t_cap_grant(src_cap, dest_cap, rights) -> 0 */
#define SYS_CAP_REVOKE 7   /* t_cap_revoke(cap) -> 0 */
#define SYS_THREAD_CREATE 8 /* t_thread_create(entry_addr, stack_addr) -> tid */
#define SYS_THREAD_YIELD  9 /* t_thread_yield() -> 0 */

/* ---- Capability rights (bitmask-encoded) ----
 * Each right is a separate bit for correct bitwise AND/OR:
 *   bit 0 = read
 *   bit 1 = write
 *   bit 2 = grant
 */
#define CAP_RIGHT_READ   1   /* bit 0 */
#define CAP_RIGHT_WRITE  2   /* bit 1 */
#define CAP_RIGHT_GRANT  4   /* bit 2 */
#define CAP_RIGHT_ALL    7   /* read | write | grant */

/* ---- Capability structure ---- */
typedef struct {
    int object_id;    /* Target kernel object */
    int rights;       /* Bitmask-encoded rights (see CAP_RIGHT_*) */
    int badge;        /* IPC badge for endpoint discrimination */
} seT5_cap;

/* ---- seT5 kernel object types ---- */
typedef enum {
    OBJ_ENDPOINT,     /* IPC endpoint */
    OBJ_NOTIFICATION, /* Async notification */
    OBJ_THREAD,       /* Thread control block */
    OBJ_MEMORY,       /* Memory frame */
    OBJ_CNODE         /* Capability node (CSpace) */
} seT5_obj_type;

/* ---- High-level API (compiles to PUSH + SYSCALL sequences) ---- */

/* Exit the current process */
static inline void t_exit(void) {
    /* In real compilation, this emits: PUSH 0, SYSCALL */
    (void)0;
}

/* Write data to a file descriptor */
static inline int t_write(int fd, int addr, int len) {
    (void)fd; (void)addr; (void)len;
    return len; /* stub */
}

/* Read data from a file descriptor */
static inline int t_read(int fd, int addr, int len) {
    (void)fd; (void)addr; (void)len;
    return 0; /* stub */
}

/* Map memory */
static inline int t_mmap(int size) {
    (void)size;
    return 0; /* stub: returns base addr */
}

/* Send a message on a capability */
static inline int t_cap_send(seT5_cap cap, int msg) {
    (void)cap; (void)msg;
    return 0;
}

/* Receive a message on a capability */
static inline int t_cap_recv(seT5_cap cap) {
    (void)cap;
    return 0;
}

/* Grant a capability with restricted rights */
static inline int t_cap_grant(seT5_cap src, seT5_cap *dest, int rights) {
    if (dest) {
        dest->object_id = src.object_id;
        dest->rights = src.rights & rights; /* intersection */
        dest->badge = src.badge;
    }
    return 0;
}

/* Revoke a capability */
static inline int t_cap_revoke(seT5_cap *cap) {
    if (cap) {
        cap->rights = 0;
        cap->badge = 0;
    }
    return 0;
}

#endif /* SET5_H */
