/*
 * test_integration.c - End-to-end integration tests
 *
 * Tests: Full pipeline: tokenize -> parse -> codegen -> vm_run
 * Verifies the compiler produces correct results for various expressions.
 */

#include "../include/test_harness.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"
#include <string.h>
#include <unistd.h>
#include <stdio.h>

/* Helper: compile expression and capture VM output */
static char output_buf[256];

static void compile_and_run(const char *expr) {
    tokenize(expr);
    parse();
    codegen();

    /* Redirect stdout to capture result */
    FILE *tmp = tmpfile();
    if (tmp == NULL) {
        output_buf[0] = '\0';
        return;
    }

    int saved_stdout = dup(fileno(stdout));
    fflush(stdout);
    dup2(fileno(tmp), fileno(stdout));

    vm_run(bytecode, bc_idx);

    fflush(stdout);
    dup2(saved_stdout, fileno(stdout));
    close(saved_stdout);

    rewind(tmp);
    size_t n = fread(output_buf, 1, sizeof(output_buf) - 1, tmp);
    output_buf[n] = '\0';
    fclose(tmp);
}

/* ---- Integration: full pipeline tests ---- */

TEST(test_e2e_simple_number) {
    compile_and_run("42");
    ASSERT_STR_EQ(output_buf, "Result: 42\n");
}

TEST(test_e2e_addition) {
    compile_and_run("10 + 20");
    ASSERT_STR_EQ(output_buf, "Result: 30\n");
}

TEST(test_e2e_multiplication) {
    compile_and_run("6 * 7");
    ASSERT_STR_EQ(output_buf, "Result: 42\n");
}

TEST(test_e2e_precedence_mul_add) {
    compile_and_run("1 + 2 * 3");
    ASSERT_STR_EQ(output_buf, "Result: 7\n");
}

TEST(test_e2e_chained_add) {
    compile_and_run("1 + 2 + 3 + 4");
    ASSERT_STR_EQ(output_buf, "Result: 10\n");
}

TEST(test_e2e_chained_mul) {
    compile_and_run("2 * 3 * 4");
    ASSERT_STR_EQ(output_buf, "Result: 24\n");
}

TEST(test_e2e_complex_expression) {
    /* 5 + 2 * 3 + 4 * 1 = 5 + 6 + 4 = 15 */
    compile_and_run("5 + 2 * 3 + 4 * 1");
    ASSERT_STR_EQ(output_buf, "Result: 15\n");
}

TEST(test_e2e_zero) {
    compile_and_run("0");
    ASSERT_STR_EQ(output_buf, "Result: 0\n");
}

int main(void) {
    TEST_SUITE_BEGIN("Integration (E2E)");

    RUN_TEST(test_e2e_simple_number);
    RUN_TEST(test_e2e_addition);
    RUN_TEST(test_e2e_multiplication);
    RUN_TEST(test_e2e_precedence_mul_add);
    RUN_TEST(test_e2e_chained_add);
    RUN_TEST(test_e2e_chained_mul);
    RUN_TEST(test_e2e_complex_expression);
    RUN_TEST(test_e2e_zero);

    TEST_SUITE_END();
}
