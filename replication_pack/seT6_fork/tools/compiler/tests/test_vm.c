/*
 * test_vm.c - Unit tests for the ternary VM
 *
 * Tests: vm_run() stack execution with various bytecode programs
 * Coverage: PUSH, ADD, MUL, HALT, stack behavior
 *
 * Note: We capture VM output by redirecting stdout to a buffer,
 * then verify the printed "Result: N" string.
 */

#include "../include/test_harness.h"
#include "../include/vm.h"
#include <string.h>
#include <unistd.h>

/* Helper: Run bytecode and capture stdout to buffer */
static char output_buf[256];

static void run_and_capture(unsigned char *code, size_t len) {
    /* Redirect stdout to a temp file, run, read back */
    FILE *tmp = tmpfile();
    if (tmp == NULL) {
        output_buf[0] = '\0';
        return;
    }

    /* Save stdout, redirect */
    int saved_stdout = dup(fileno(stdout));
    fflush(stdout);
    dup2(fileno(tmp), fileno(stdout));

    vm_run(code, len);

    /* Restore stdout */
    fflush(stdout);
    dup2(saved_stdout, fileno(stdout));
    close(saved_stdout);

    /* Read captured output */
    rewind(tmp);
    size_t n = fread(output_buf, 1, sizeof(output_buf) - 1, tmp);
    output_buf[n] = '\0';
    fclose(tmp);
}

/* ---- PUSH + HALT ---- */

TEST(test_vm_push_halt) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 5, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 5\n");
}

TEST(test_vm_push_zero) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 0, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 0\n");
}

/* ---- ADD ---- */

TEST(test_vm_simple_add) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 3, OP_PUSH, 4, OP_ADD, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
}

TEST(test_vm_add_zero) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 0, OP_ADD, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 5\n");
}

/* ---- MUL ---- */

TEST(test_vm_simple_mul) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 3, OP_PUSH, 4, OP_MUL, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 12\n");
}

TEST(test_vm_mul_zero) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 0, OP_MUL, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 0\n");
}

TEST(test_vm_mul_one) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 7, OP_PUSH, 1, OP_MUL, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
}

/* ---- Combined: 1 + 2 * 3 = 7 ---- */

TEST(test_vm_expression_1_plus_2_mul_3) {
    vm_memory_reset();
    unsigned char code[] = {
        OP_PUSH, 1,
        OP_PUSH, 2,
        OP_PUSH, 3,
        OP_MUL,
        OP_ADD,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
}

/* ---- Chained ADD: 1 + 2 + 3 = 6 ---- */

TEST(test_vm_chained_add) {
    vm_memory_reset();
    unsigned char code[] = {
        OP_PUSH, 1,
        OP_PUSH, 2,
        OP_ADD,
        OP_PUSH, 3,
        OP_ADD,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 6\n");
}

/* ---- Chained MUL: 2 * 3 * 4 = 24 ---- */

TEST(test_vm_chained_mul) {
    vm_memory_reset();
    unsigned char code[] = {
        OP_PUSH, 2,
        OP_PUSH, 3,
        OP_MUL,
        OP_PUSH, 4,
        OP_MUL,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 24\n");
}

/* ---- JMP: unconditional jump (TASK-003) ---- */

TEST(test_vm_jmp) {
    vm_memory_reset();
    /* PUSH 99, JMP to byte 6 (skip PUSH 42), HALT */
    unsigned char code[] = {
        OP_PUSH, 99,
        OP_JMP, 6,
        OP_PUSH, 42,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 99\n");
}

/* ---- COND_JMP: jump if top of stack == 0 (TASK-003) ---- */

TEST(test_vm_cond_jmp_true) {
    vm_memory_reset();
    /* PUSH 10, PUSH 0 (condition=0 -> jump), COND_JMP 8, PUSH 20 (skipped), HALT */
    unsigned char code[] = {
        OP_PUSH, 10,
        OP_PUSH, 0,
        OP_COND_JMP, 8,
        OP_PUSH, 20,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 10\n");
}

TEST(test_vm_cond_jmp_false) {
    vm_memory_reset();
    /* PUSH 10, PUSH 1 (condition!=0 -> no jump), COND_JMP 8, PUSH 20, HALT */
    unsigned char code[] = {
        OP_PUSH, 10,
        OP_PUSH, 1,
        OP_COND_JMP, 8,
        OP_PUSH, 20,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 20\n");
}

/* ====== Phase 3: Stack manipulation tests (Setun-70 postfix) ====== */

TEST(test_vm_dup) {
    vm_memory_reset();
    /* PUSH 7, DUP, ADD -> 7 + 7 = 14 */
    unsigned char code[] = {OP_PUSH, 7, OP_DUP, OP_ADD, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 14\n");
}

TEST(test_vm_drop) {
    vm_memory_reset();
    /* PUSH 5, PUSH 99, DROP -> 5 remains */
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 99, OP_DROP, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 5\n");
}

TEST(test_vm_swap) {
    vm_memory_reset();
    /* PUSH 3, PUSH 10, SWAP, SUB -> 10 - 3 = 7 */
    unsigned char code[] = {OP_PUSH, 3, OP_PUSH, 10, OP_SWAP, OP_SUB, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
}

TEST(test_vm_over) {
    vm_memory_reset();
    /* PUSH 2, PUSH 5, OVER, ADD -> 2 + 5 + 2 on stack, ADD gives 5+2=7, stack: 2 7 */
    /* Actually: OVER gives (2 5 2), ADD gives (2 7), result = 7 */
    unsigned char code[] = {OP_PUSH, 2, OP_PUSH, 5, OP_OVER, OP_ADD, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
}

TEST(test_vm_rot) {
    vm_memory_reset();
    /* PUSH 1, PUSH 2, PUSH 3, ROT -> (2 3 1), ADD -> (2 4), result = 4 */
    unsigned char code[] = {OP_PUSH, 1, OP_PUSH, 2, OP_PUSH, 3, OP_ROT, OP_ADD, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 4\n");
}

/* ====== Phase 3: Return stack tests (two-stack model) ====== */

TEST(test_vm_return_stack) {
    vm_memory_reset();
    /* PUSH 42, TO_R, PUSH 10, FROM_R, ADD -> 10 + 42 = 52 */
    unsigned char code[] = {
        OP_PUSH, 42, OP_TO_R,
        OP_PUSH, 10, OP_FROM_R,
        OP_ADD,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 52\n");
}

TEST(test_vm_r_fetch) {
    vm_memory_reset();
    /* PUSH 7, TO_R, R_FETCH, R_FETCH, ADD, FROM_R, DROP -> 7 + 7 = 14 */
    unsigned char code[] = {
        OP_PUSH, 7, OP_TO_R,
        OP_R_FETCH, OP_R_FETCH, OP_ADD,
        OP_FROM_R, OP_DROP,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 14\n");
}

/* ====== Phase 3: Comparison ops ====== */

TEST(test_vm_cmp_eq_true) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 5, OP_CMP_EQ, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 1\n");
}

TEST(test_vm_cmp_eq_false) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 3, OP_CMP_EQ, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 0\n");
}

TEST(test_vm_cmp_lt) {
    vm_memory_reset();
    /* 3 < 5 -> 1 */
    unsigned char code[] = {OP_PUSH, 3, OP_PUSH, 5, OP_CMP_LT, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 1\n");
}

TEST(test_vm_cmp_gt) {
    vm_memory_reset();
    /* 10 > 3 -> 1 */
    unsigned char code[] = {OP_PUSH, 10, OP_PUSH, 3, OP_CMP_GT, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 1\n");
}

/* ====== Phase 3: Ternary logic gates (Brusentsov/Jones) ====== */

TEST(test_vm_ternary_neg) {
    vm_memory_reset();
    unsigned char code[] = {OP_PUSH, 5, OP_NEG, OP_HALT};
    run_and_capture(code, sizeof(code));
    /* -5 is sign-extended in output */
    ASSERT_EQ(vm_get_result(), -5);
}

TEST(test_vm_consensus) {
    vm_memory_reset();
    /* consensus(5, 3): trit-level min of balanced ternary representations
     * 5 = [-1,-1,+1,...], 3 = [0,+1,0,...]
     * min per trit: [-1,-1,0,...] = -1 - 3 = -4 */
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 3, OP_CONSENSUS, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_EQ(vm_get_result(), -4);
}

TEST(test_vm_accept_any) {
    vm_memory_reset();
    /* accept_any(5, 3): trit-level max
     * 5 = [-1,-1,+1,...], 3 = [0,+1,0,...]
     * max per trit: [0,+1,+1,...] = 0 + 3 + 9 = 12 */
    unsigned char code[] = {OP_PUSH, 5, OP_PUSH, 3, OP_ACCEPT_ANY, OP_HALT};
    run_and_capture(code, sizeof(code));
    ASSERT_EQ(vm_get_result(), 12);
}

/* ====== Phase 3: BRZ/BRN/BRP structured branching ====== */

TEST(test_vm_brz_taken) {
    vm_memory_reset();
    /* PUSH 0, BRZ 6, PUSH 99 (skipped), PUSH 42, HALT */
    unsigned char code[] = {
        OP_PUSH, 0,
        OP_BRZ, 6,
        OP_PUSH, 99,
        OP_PUSH, 42,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 42\n");
}

TEST(test_vm_brz_not_taken) {
    vm_memory_reset();
    unsigned char code[] = {
        OP_PUSH, 1,
        OP_BRZ, 6,
        OP_PUSH, 99,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 99\n");
}

/* ====== Phase 3: ENTER/LEAVE scope ====== */

TEST(test_vm_enter_leave) {
    vm_memory_reset();
    /* ENTER pushes sentinel, LEAVE pops back */
    unsigned char code[] = {
        OP_ENTER,
        OP_PUSH, 42, OP_TO_R,
        OP_LEAVE,
        OP_PUSH, 7,
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
    /* After LEAVE, return stack should be clean */
    ASSERT_EQ(vm_rstack_depth(), 0);
}

/* ====== Phase 3: LOOP_BEGIN/LOOP_END ====== */

TEST(test_vm_loop) {
    vm_memory_reset();
    /* Sum 1+2+3: start with 0, loop 3 times adding counter */
    /* mem[0] = sum, mem[1] = counter (starts at 3) */
    unsigned char code[] = {
        OP_PUSH, 0, OP_PUSH, 0, OP_STORE,   /* mem[0] = 0 (sum) */
        OP_PUSH, 1, OP_PUSH, 3, OP_STORE,   /* mem[1] = 3 (counter) */
        OP_LOOP_BEGIN,                        /* loop start */
        /* sum += counter */
        OP_PUSH, 0,                          /* addr for sum */
        OP_PUSH, 0, OP_LOAD,                /* load sum */
        OP_PUSH, 1, OP_LOAD,                /* load counter */
        OP_ADD,                              /* sum + counter */
        OP_STORE,                            /* store back to mem[0] */
        /* counter-- */
        OP_PUSH, 1,                          /* addr for counter */
        OP_PUSH, 1, OP_LOAD,                /* load counter */
        OP_PUSH, 1, OP_SUB,                 /* counter - 1 */
        OP_STORE,                            /* store back */
        /* loop condition: counter > 0 */
        OP_PUSH, 1, OP_LOAD,                /* load counter */
        OP_LOOP_END,                         /* if != 0, loop back */
        /* result */
        OP_PUSH, 0, OP_LOAD,                /* load sum */
        OP_HALT
    };
    run_and_capture(code, sizeof(code));
    ASSERT_STR_EQ(output_buf, "Result: 6\n");
}

int main(void) {
    TEST_SUITE_BEGIN("VM Execution");

    /* Phase 1: Core ops */
    RUN_TEST(test_vm_push_halt);
    RUN_TEST(test_vm_push_zero);
    RUN_TEST(test_vm_simple_add);
    RUN_TEST(test_vm_add_zero);
    RUN_TEST(test_vm_simple_mul);
    RUN_TEST(test_vm_mul_zero);
    RUN_TEST(test_vm_mul_one);
    RUN_TEST(test_vm_expression_1_plus_2_mul_3);
    RUN_TEST(test_vm_chained_add);
    RUN_TEST(test_vm_chained_mul);
    RUN_TEST(test_vm_jmp);
    RUN_TEST(test_vm_cond_jmp_true);
    RUN_TEST(test_vm_cond_jmp_false);

    /* Phase 3: Stack manipulation (Setun-70 postfix) */
    RUN_TEST(test_vm_dup);
    RUN_TEST(test_vm_drop);
    RUN_TEST(test_vm_swap);
    RUN_TEST(test_vm_over);
    RUN_TEST(test_vm_rot);

    /* Phase 3: Return stack (two-stack model) */
    RUN_TEST(test_vm_return_stack);
    RUN_TEST(test_vm_r_fetch);

    /* Phase 3: Comparison ops */
    RUN_TEST(test_vm_cmp_eq_true);
    RUN_TEST(test_vm_cmp_eq_false);
    RUN_TEST(test_vm_cmp_lt);
    RUN_TEST(test_vm_cmp_gt);

    /* Phase 3: Ternary logic gates */
    RUN_TEST(test_vm_ternary_neg);
    RUN_TEST(test_vm_consensus);
    RUN_TEST(test_vm_accept_any);

    /* Phase 3: Structured branching */
    RUN_TEST(test_vm_brz_taken);
    RUN_TEST(test_vm_brz_not_taken);

    /* Phase 3: Scope management */
    RUN_TEST(test_vm_enter_leave);

    /* Phase 3: Loop */
    RUN_TEST(test_vm_loop);

    TEST_SUITE_END();
}
