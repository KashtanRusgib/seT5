/*
 * test_arrays.c - Array support tests (Phase 3)
 * Tests array declaration, access, assignment via bootstrap pipeline.
 */

#include <stdio.h>
#include <string.h>
#include "../include/test_harness.h"
#include "../include/bootstrap.h"
#include "../include/ir.h"
#include "../include/parser.h"
#include "../include/vm.h"

/* === IR-level array tests === */

TEST(test_create_array_decl) {
    Expr *e = create_array_decl("arr", 5, NULL, 0);
    ASSERT_NOT_NULL(e);
    ASSERT_EQ(e->type, NODE_ARRAY_DECL);
    ASSERT_STR_EQ(e->name, "arr");
    ASSERT_EQ(e->array_size, 5);
    ASSERT_EQ(e->param_count, 0);
    expr_free(e);
}

TEST(test_create_array_decl_with_init) {
    Expr **inits = (Expr **)malloc(3 * sizeof(Expr *));
    inits[0] = create_const(10);
    inits[1] = create_const(20);
    inits[2] = create_const(30);
    Expr *e = create_array_decl("data", 3, inits, 3);
    ASSERT_NOT_NULL(e);
    ASSERT_EQ(e->array_size, 3);
    ASSERT_EQ(e->param_count, 3);
    ASSERT_EQ(e->params[0]->val, 10);
    ASSERT_EQ(e->params[1]->val, 20);
    ASSERT_EQ(e->params[2]->val, 30);
    expr_free(e);
}

TEST(test_create_array_access) {
    Expr *idx = create_const(2);
    Expr *e = create_array_access("arr", idx);
    ASSERT_NOT_NULL(e);
    ASSERT_EQ(e->type, NODE_ARRAY_ACCESS);
    ASSERT_STR_EQ(e->name, "arr");
    ASSERT_EQ(e->left->val, 2);
    expr_free(e);
}

TEST(test_create_array_assign) {
    Expr *idx = create_const(1);
    Expr *val = create_const(42);
    Expr *e = create_array_assign("buf", idx, val);
    ASSERT_NOT_NULL(e);
    ASSERT_EQ(e->type, NODE_ARRAY_ASSIGN);
    ASSERT_STR_EQ(e->name, "buf");
    ASSERT_EQ(e->left->val, 1);
    ASSERT_EQ(e->right->val, 42);
    expr_free(e);
}

/* === Parser-level array tests === */

TEST(test_parse_array_decl) {
    const char *src = "int main() { int arr[3]; return 0; }";
    Expr *prog = parse_program(src);
    ASSERT_NOT_NULL(prog);
    ASSERT_EQ(prog->type, NODE_PROGRAM);
    /* main function -> body should be return 0, with arr decl as a param stmt */
    expr_free(prog);
}

TEST(test_parse_array_decl_init) {
    const char *src = "int main() { int arr[3] = {1, 2, 3}; return 0; }";
    Expr *prog = parse_program(src);
    ASSERT_NOT_NULL(prog);
    expr_free(prog);
}

TEST(test_parse_array_access) {
    const char *src = "int main() { int arr[3]; return arr[0]; }";
    Expr *prog = parse_program(src);
    ASSERT_NOT_NULL(prog);
    expr_free(prog);
}

TEST(test_parse_array_assign) {
    const char *src = "int main() { int arr[3]; arr[1] = 42; return 0; }";
    Expr *prog = parse_program(src);
    ASSERT_NOT_NULL(prog);
    expr_free(prog);
}

/* === Bootstrap compilation of array code === */

TEST(test_compile_array_init_and_access) {
    /* Compile: declare array, initialize, read back */
    const char *src =
        "int main() {\n"
        "    int arr[3] = {10, 20, 30};\n"
        "    return arr[1];\n"
        "}\n";

    unsigned char code[1024];
    int len = bootstrap_compile(src, code, 1024);
    ASSERT_TRUE(len > 0);

    vm_memory_reset();
    vm_run(code, (size_t)len);
    int result = vm_get_result();
    ASSERT_EQ(result, 20);
}

TEST(test_compile_array_assign_and_read) {
    const char *src =
        "int main() {\n"
        "    int arr[3];\n"
        "    arr[0] = 5;\n"
        "    arr[1] = 10;\n"
        "    arr[2] = arr[0] + arr[1];\n"
        "    return arr[2];\n"
        "}\n";

    unsigned char code[1024];
    int len = bootstrap_compile(src, code, 1024);
    ASSERT_TRUE(len > 0);

    vm_memory_reset();
    vm_run(code, (size_t)len);
    int result = vm_get_result();
    ASSERT_EQ(result, 15);
}

TEST(test_compile_array_with_loop) {
    /* Sum array elements using a for loop */
    const char *src =
        "int main() {\n"
        "    int arr[3] = {1, 2, 3};\n"
        "    int sum = 0;\n"
        "    for (int i = 0; i < 3; i++) {\n"
        "        sum = sum + arr[i];\n"
        "    }\n"
        "    return sum;\n"
        "}\n";

    unsigned char code[1024];
    int len = bootstrap_compile(src, code, 1024);
    ASSERT_TRUE(len > 0);

    vm_memory_reset();
    vm_run(code, (size_t)len);
    int result = vm_get_result();
    ASSERT_EQ(result, 6);
}

/* === Optimizer tests for arrays === */

TEST(test_optimize_array_const_index) {
    /* Array access with constant index should survive optimization */
    Expr *idx = create_const(2);
    Expr *access = create_array_access("x", idx);
    optimize(access);
    ASSERT_EQ(access->type, NODE_ARRAY_ACCESS);
    ASSERT_EQ(access->left->val, 2);
    expr_free(access);
}

int main(void) {
    TEST_SUITE_BEGIN("Arrays");

    /* IR tests */
    RUN_TEST(test_create_array_decl);
    RUN_TEST(test_create_array_decl_with_init);
    RUN_TEST(test_create_array_access);
    RUN_TEST(test_create_array_assign);

    /* Parser tests */
    RUN_TEST(test_parse_array_decl);
    RUN_TEST(test_parse_array_decl_init);
    RUN_TEST(test_parse_array_access);
    RUN_TEST(test_parse_array_assign);

    /* Compilation tests */
    RUN_TEST(test_compile_array_init_and_access);
    RUN_TEST(test_compile_array_assign_and_read);
    RUN_TEST(test_compile_array_with_loop);

    /* Optimizer */
    RUN_TEST(test_optimize_array_const_index);

    TEST_SUITE_END();
}
