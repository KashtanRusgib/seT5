/*
 * test_codegen.c - Unit tests for bytecode generation
 *
 * Tests: codegen() emits correct bytecode for tokenized expressions
 * Coverage: simple ints, addition, multiplication, precedence
 */

#include "../include/test_harness.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"

/* ---- Single integer ---- */

TEST(test_codegen_single_int) {
    tokenize("5");
    parse();
    codegen();

    /* PUSH 5, HALT */
    ASSERT_EQ(bc_idx, 3);
    ASSERT_EQ(bytecode[0], OP_PUSH);
    ASSERT_EQ(bytecode[1], 5);
    ASSERT_EQ(bytecode[2], OP_HALT);
}

/* ---- Simple addition ---- */

TEST(test_codegen_addition) {
    tokenize("3 + 4");
    parse();
    codegen();

    /* PUSH 3, PUSH 4, ADD, HALT */
    ASSERT_EQ(bc_idx, 6);
    ASSERT_EQ(bytecode[0], OP_PUSH);
    ASSERT_EQ(bytecode[1], 3);
    ASSERT_EQ(bytecode[2], OP_PUSH);
    ASSERT_EQ(bytecode[3], 4);
    ASSERT_EQ(bytecode[4], OP_ADD);
    ASSERT_EQ(bytecode[5], OP_HALT);
}

/* ---- Simple multiplication ---- */

TEST(test_codegen_multiplication) {
    tokenize("2 * 3");
    parse();
    codegen();

    /* PUSH 2, PUSH 3, MUL, HALT */
    ASSERT_EQ(bc_idx, 6);
    ASSERT_EQ(bytecode[0], OP_PUSH);
    ASSERT_EQ(bytecode[1], 2);
    ASSERT_EQ(bytecode[2], OP_PUSH);
    ASSERT_EQ(bytecode[3], 3);
    ASSERT_EQ(bytecode[4], OP_MUL);
    ASSERT_EQ(bytecode[5], OP_HALT);
}

/* ---- Precedence: * before + ---- */

TEST(test_codegen_precedence) {
    tokenize("1 + 2 * 3");
    parse();
    codegen();

    /* PUSH 1, PUSH 2, PUSH 3, MUL, ADD, HALT */
    ASSERT_EQ(bc_idx, 9);
    ASSERT_EQ(bytecode[0], OP_PUSH);
    ASSERT_EQ(bytecode[1], 1);
    ASSERT_EQ(bytecode[2], OP_PUSH);
    ASSERT_EQ(bytecode[3], 2);
    ASSERT_EQ(bytecode[4], OP_PUSH);
    ASSERT_EQ(bytecode[5], 3);
    ASSERT_EQ(bytecode[6], OP_MUL);
    ASSERT_EQ(bytecode[7], OP_ADD);
    ASSERT_EQ(bytecode[8], OP_HALT);
}

/* ---- Chained addition ---- */

TEST(test_codegen_chained_add) {
    tokenize("1 + 2 + 3");
    parse();
    codegen();

    /* PUSH 1, PUSH 2, ADD, PUSH 3, ADD, HALT = 9 bytes */
    ASSERT_EQ(bc_idx, 9);
    ASSERT_EQ(bytecode[0], OP_PUSH);
    ASSERT_EQ(bytecode[1], 1);
    ASSERT_EQ(bytecode[2], OP_PUSH);
    ASSERT_EQ(bytecode[3], 2);
    ASSERT_EQ(bytecode[4], OP_ADD);
    ASSERT_EQ(bytecode[5], OP_PUSH);
    ASSERT_EQ(bytecode[6], 3);
    ASSERT_EQ(bytecode[7], OP_ADD);
    ASSERT_EQ(bytecode[8], OP_HALT);
}

/* ---- Chained multiplication ---- */

TEST(test_codegen_chained_mul) {
    tokenize("2 * 3 * 4");
    parse();
    codegen();

    /* PUSH 2, PUSH 3, MUL, PUSH 4, MUL, HALT */
    ASSERT_EQ(bc_idx, 9);
    ASSERT_EQ(bytecode[0], OP_PUSH);
    ASSERT_EQ(bytecode[1], 2);
    ASSERT_EQ(bytecode[2], OP_PUSH);
    ASSERT_EQ(bytecode[3], 3);
    ASSERT_EQ(bytecode[4], OP_MUL);
    ASSERT_EQ(bytecode[5], OP_PUSH);
    ASSERT_EQ(bytecode[6], 4);
    ASSERT_EQ(bytecode[7], OP_MUL);
    ASSERT_EQ(bytecode[8], OP_HALT);
}

/* ---- Bytecode always ends with HALT ---- */

TEST(test_codegen_halt_termination) {
    tokenize("7");
    parse();
    codegen();
    ASSERT_TRUE(bc_idx > 0);
    ASSERT_EQ(bytecode[bc_idx - 1], OP_HALT);
}

int main(void) {
    TEST_SUITE_BEGIN("Code Generator");

    RUN_TEST(test_codegen_single_int);
    RUN_TEST(test_codegen_addition);
    RUN_TEST(test_codegen_multiplication);
    RUN_TEST(test_codegen_precedence);
    RUN_TEST(test_codegen_chained_add);
    RUN_TEST(test_codegen_chained_mul);
    RUN_TEST(test_codegen_halt_termination);

    TEST_SUITE_END();
}
