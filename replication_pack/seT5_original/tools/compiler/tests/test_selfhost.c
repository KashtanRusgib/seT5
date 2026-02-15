/*
 * test_selfhost.c - Phase 5: Self-Hosting Compiler Tests
 *
 * Tests that the Ternary-C compiler can compile meaningful subsets
 * of its own source code (seT5-C) and produce correct results on
 * the ternary VM.
 */

#include "../include/test_harness.h"
#include "../include/selfhost.h"
#include "../include/bootstrap.h"
#include "../include/vm.h"

/* === Roundtrip tests: compile seT5-C → bytecode → run on VM → verify result === */

TEST(test_selfhost_identity) {
    /* Simplest roundtrip: return a constant */
    ASSERT_EQ(selfhost_roundtrip_test("int main() { return 42; }\n", 42), 0);
}

TEST(test_selfhost_arithmetic) {
    /* Arithmetic expressions */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int a = 3;\n"
        "    int b = 4;\n"
        "    int c = a + b;\n"
        "    int d = c * 2;\n"
        "    return d;\n"
        "}\n", 14), 0);
}

TEST(test_selfhost_subtraction) {
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int x = 10;\n"
        "    int y = 3;\n"
        "    return x - y;\n"
        "}\n", 7), 0);
}

TEST(test_selfhost_nested_arithmetic) {
    /* (2 + 3) * (4 + 1) = 25 */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int a = 2 + 3;\n"
        "    int b = 4 + 1;\n"
        "    return a * b;\n"
        "}\n", 25), 0);
}

TEST(test_selfhost_while_loop) {
    /* sum(1..5) = 15 */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int sum = 0;\n"
        "    int i = 1;\n"
        "    while (i < 6) {\n"
        "        sum = sum + i;\n"
        "        i = i + 1;\n"
        "    }\n"
        "    return sum;\n"
        "}\n", 15), 0);
}

TEST(test_selfhost_if_true) {
    /* Conditional: takes the true branch */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int x = 10;\n"
        "    int y = 20;\n"
        "    int result = 0;\n"
        "    if (x < y) {\n"
        "        result = x + y;\n"
        "    }\n"
        "    return result;\n"
        "}\n", 30), 0);
}

TEST(test_selfhost_if_false) {
    /* Conditional: condition false, result stays 0 */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int x = 20;\n"
        "    int y = 10;\n"
        "    int result = 5;\n"
        "    if (x < y) {\n"
        "        result = 99;\n"
        "    }\n"
        "    return result;\n"
        "}\n", 5), 0);
}

TEST(test_selfhost_multiple_vars) {
    /* Multiple variable declarations and reassignments */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int a = 1;\n"
        "    int b = 2;\n"
        "    int c = 3;\n"
        "    a = a + b;\n"
        "    b = b + c;\n"
        "    c = a + b;\n"
        "    return c;\n"
        "}\n", 8), 0); /* a=3, b=5, c=3+5=8 */
}

TEST(test_selfhost_factorial_like) {
    /* Iterative computation: 1*2*3*4 = 24 */
    ASSERT_EQ(selfhost_roundtrip_test(
        "int main() {\n"
        "    int result = 1;\n"
        "    int i = 2;\n"
        "    while (i < 5) {\n"
        "        result = result * i;\n"
        "        i = i + 1;\n"
        "    }\n"
        "    return result;\n"
        "}\n", 24), 0);
}

/* === Tokenizer compilation tests === */

TEST(test_selfhost_tokenizer_compiles) {
    /* Verify the self-hosted tokenizer compiles to valid bytecode */
    unsigned char bytecode[MAX_BYTECODE];
    int len = selfhost_compile_tokenizer(bytecode, MAX_BYTECODE);
    ASSERT_GT(len, 0);
    /* Last byte should be HALT */
    ASSERT_EQ(bytecode[len - 1], OP_HALT);
}

TEST(test_selfhost_tokenizer_bytecode_reasonable) {
    /* Check bytecode size is reasonable (not degenerate) */
    unsigned char bytecode[MAX_BYTECODE];
    int len = selfhost_compile_tokenizer(bytecode, MAX_BYTECODE);
    /* The tokenizer has substantial logic; expect at least 50 bytes */
    ASSERT_GT(len, 50);
    /* But not ridiculously large (< 1000 bytes) */
    ASSERT_LT(len, 1000);
}

/* === Self-hosting verification test === */

TEST(test_selfhost_verify) {
    SelfHostResult result;
    selfhost_verify(&result);
    ASSERT_EQ(result.compilation_ok, 1);
    ASSERT_EQ(result.execution_ok, 1);
    ASSERT_GT(result.bytecode_len, 0);
}

/* === Bootstrap self-test === */

TEST(test_bootstrap_self_test) {
    ASSERT_EQ(bootstrap_self_test(), 0);
}

int main(void) {
    TEST_SUITE_BEGIN("Self-Hosting (Phase 5)");

    /* Roundtrip tests */
    RUN_TEST(test_selfhost_identity);
    RUN_TEST(test_selfhost_arithmetic);
    RUN_TEST(test_selfhost_subtraction);
    RUN_TEST(test_selfhost_nested_arithmetic);
    RUN_TEST(test_selfhost_while_loop);
    RUN_TEST(test_selfhost_if_true);
    RUN_TEST(test_selfhost_if_false);
    RUN_TEST(test_selfhost_multiple_vars);
    RUN_TEST(test_selfhost_factorial_like);

    /* Tokenizer compilation */
    RUN_TEST(test_selfhost_tokenizer_compiles);
    RUN_TEST(test_selfhost_tokenizer_bytecode_reasonable);

    /* Full verification */
    RUN_TEST(test_selfhost_verify);
    RUN_TEST(test_bootstrap_self_test);

    TEST_SUITE_END();
}
