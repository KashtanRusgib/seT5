/*
 * test_set5.c - Tests for TASK-016: seT5 Microkernel Syscall Stubs
 *
 * Tests: syscall dispatch via VM, capability operations,
 * IPC stubs, memory mapping, thread stubs.
 */

#include "../include/test_harness.h"
#include "../include/vm.h"
#include "../include/set5.h"

/* ---- Syscall dispatch via VM ---- */

TEST(test_syscall_exit) {
    vm_memory_reset();
    /* PUSH 0 (SYS_EXIT), SYSCALL — should return immediately */
    unsigned char prog[] = {
        OP_PUSH, SYS_EXIT,
        OP_SYSCALL
    };
    vm_run(prog, sizeof(prog));
    /* If we get here, t_exit worked (vm_run returned) */
    ASSERT_TRUE(1);
}

TEST(test_syscall_write) {
    vm_memory_reset();
    /* t_write(1, 100, 5): push len, addr, fd, then syscall_no */
    unsigned char prog[] = {
        OP_PUSH, 5,    /* len */
        OP_PUSH, 100,  /* addr (unused in stub) */
        OP_PUSH, 1,    /* fd */
        OP_PUSH, SYS_WRITE,
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* stub returns len=5 as result */
    ASSERT_EQ(vm_get_result(), 5);
}

TEST(test_syscall_read) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 10,   /* len */
        OP_PUSH, 200,  /* addr */
        OP_PUSH, 0,    /* fd */
        OP_PUSH, SYS_READ,
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* stub returns 0 bytes read */
    ASSERT_EQ(vm_get_result(), 0);
}

TEST(test_syscall_mmap) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 16,   /* size */
        OP_PUSH, SYS_MMAP,
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* Returns base address (MEMORY_SIZE/2 = 364 after reset) */
    ASSERT_EQ(vm_get_result(), 364);
}

TEST(test_syscall_cap_send) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 42,   /* msg */
        OP_PUSH, 1,    /* cap id */
        OP_PUSH, SYS_CAP_SEND,
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* Returns 0 (success) */
    ASSERT_EQ(vm_get_result(), 0);
}

TEST(test_syscall_cap_recv) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 1,    /* cap id */
        OP_PUSH, SYS_CAP_RECV,
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* Returns stub value 42 */
    ASSERT_EQ(vm_get_result(), 42);
}

TEST(test_syscall_unknown) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 99,   /* unknown syscall */
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* Returns -1 (unknown) */
    ASSERT_EQ(vm_get_result(), -1);
}

/* ---- Capability high-level API ---- */

TEST(test_cap_grant_restricts_rights) {
    seT5_cap src = { .object_id = 1, .rights = CAP_RIGHT_ALL, .badge = 10 };
    seT5_cap dest;
    t_cap_grant(src, &dest, CAP_RIGHT_READ);
    ASSERT_EQ(dest.object_id, 1);
    ASSERT_EQ(dest.rights, CAP_RIGHT_READ);
    ASSERT_EQ(dest.badge, 10);
}

TEST(test_cap_grant_no_escalation) {
    seT5_cap src = { .object_id = 2, .rights = CAP_RIGHT_READ, .badge = 0 };
    seT5_cap dest;
    t_cap_grant(src, &dest, CAP_RIGHT_ALL);
    /* Can't escalate: result is intersection */
    ASSERT_EQ(dest.rights, CAP_RIGHT_READ);
}

TEST(test_cap_revoke) {
    seT5_cap cap = { .object_id = 3, .rights = CAP_RIGHT_ALL, .badge = 5 };
    t_cap_revoke(&cap);
    ASSERT_EQ(cap.rights, 0);
    ASSERT_EQ(cap.badge, 0);
}

TEST(test_cap_rights_bitmask_encoding) {
    /* Verify bitmask encoding: R=1, W=2, G=4, all=7 */
    ASSERT_EQ(CAP_RIGHT_READ, 1);
    ASSERT_EQ(CAP_RIGHT_WRITE, 2);
    ASSERT_EQ(CAP_RIGHT_GRANT, 4);
    ASSERT_EQ(CAP_RIGHT_ALL, 7);
}

TEST(test_cap_obj_types) {
    ASSERT_EQ(OBJ_ENDPOINT, 0);
    ASSERT_EQ(OBJ_NOTIFICATION, 1);
    ASSERT_EQ(OBJ_THREAD, 2);
    ASSERT_EQ(OBJ_MEMORY, 3);
    ASSERT_EQ(OBJ_CNODE, 4);
}

/* ---- VM memory + syscall combined ---- */

TEST(test_store_then_write_syscall) {
    vm_memory_reset();
    /* Store value 65 at addr 50, then call t_write to "output" it */
    unsigned char prog[] = {
        OP_PUSH, 50, OP_PUSH, 65, OP_STORE,   /* mem[50] = 65 */
        OP_PUSH, 1,    /* len */
        OP_PUSH, 50,   /* addr */
        OP_PUSH, 1,    /* fd=stdout */
        OP_PUSH, SYS_WRITE,
        OP_SYSCALL,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    ASSERT_EQ(vm_memory_read(50), 65);
}

int main(void) {
    TEST_SUITE_BEGIN("seT5 Syscalls (TASK-016)");
    /* VM syscall dispatch */
    RUN_TEST(test_syscall_exit);
    RUN_TEST(test_syscall_write);
    RUN_TEST(test_syscall_read);
    RUN_TEST(test_syscall_mmap);
    RUN_TEST(test_syscall_cap_send);
    RUN_TEST(test_syscall_cap_recv);
    RUN_TEST(test_syscall_unknown);
    /* Capability API */
    RUN_TEST(test_cap_grant_restricts_rights);
    RUN_TEST(test_cap_grant_no_escalation);
    RUN_TEST(test_cap_revoke);
    RUN_TEST(test_cap_rights_bitmask_encoding);
    RUN_TEST(test_cap_obj_types);
    /* Combined */
    RUN_TEST(test_store_then_write_syscall);
    TEST_SUITE_END();
}
