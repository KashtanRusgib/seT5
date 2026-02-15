/*
 * test_typechecker.c - Type checker tests (Phase 3)
 * Tests type inference, error detection, and array bounds checking.
 */

#include <stdio.h>
#include <string.h>
#include "../include/test_harness.h"
#include "../include/typechecker.h"
#include "../include/ir.h"
#include "../include/parser.h"

/* === Basic type inference === */

TEST(test_const_is_int) {
    TypeChecker tc;
    typechecker_init(&tc);
    Expr *e = create_const(42);
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_INT);
    expr_free(e);
}

TEST(test_var_declared) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc int_t = {TYPE_INT, 0};
    typechecker_add_symbol(&tc, "x", int_t);

    Expr *e = create_var("x");
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_INT);
    expr_free(e);
}

TEST(test_var_undeclared) {
    TypeChecker tc;
    typechecker_init(&tc);
    Expr *e = create_var("unknown");
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_UNKNOWN);
    ASSERT_EQ(tc.error_count, 1);
    expr_free(e);
}

TEST(test_binop_int) {
    TypeChecker tc;
    typechecker_init(&tc);
    Expr *e = create_binop(OP_IR_ADD, create_const(1), create_const(2));
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_INT);
    ASSERT_EQ(tc.error_count, 0);
    expr_free(e);
}

TEST(test_comparison_returns_int) {
    TypeChecker tc;
    typechecker_init(&tc);
    Expr *e = create_binop(OP_IR_CMP_EQ, create_const(1), create_const(1));
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_INT);
    expr_free(e);
}

/* === Pointer type checking === */

TEST(test_addr_of_returns_ptr) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc int_t = {TYPE_INT, 0};
    typechecker_add_symbol(&tc, "x", int_t);

    Expr *e = create_addr_of(create_var("x"));
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_PTR);
    expr_free(e);
}

TEST(test_deref_ptr) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc ptr_t = {TYPE_PTR, 0};
    typechecker_add_symbol(&tc, "p", ptr_t);

    Expr *inner = create_var("p");
    Expr *e = create_deref(inner);
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_INT);
    ASSERT_EQ(tc.error_count, 0);
    expr_free(e);
}

TEST(test_deref_non_ptr_error) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc int_t = {TYPE_INT, 0};
    typechecker_add_symbol(&tc, "x", int_t);

    Expr *e = create_deref(create_var("x"));
    typechecker_infer(&tc, e);
    ASSERT_EQ(tc.error_count, 1); /* deref of non-pointer */
    expr_free(e);
}

/* === Array type checking === */

TEST(test_array_access_valid) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc arr_t = {TYPE_ARRAY, 5};
    typechecker_add_symbol(&tc, "arr", arr_t);

    Expr *e = create_array_access("arr", create_const(2));
    TypeDesc t = typechecker_infer(&tc, e);
    ASSERT_EQ(t.kind, TYPE_INT);
    ASSERT_EQ(tc.error_count, 0);
    expr_free(e);
}

TEST(test_array_bounds_error) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc arr_t = {TYPE_ARRAY, 3};
    typechecker_add_symbol(&tc, "arr", arr_t);

    Expr *e = create_array_access("arr", create_const(5));
    typechecker_infer(&tc, e);
    ASSERT_EQ(tc.error_count, 1); /* out of bounds */
    expr_free(e);
}

TEST(test_array_negative_index_error) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc arr_t = {TYPE_ARRAY, 3};
    typechecker_add_symbol(&tc, "arr", arr_t);

    Expr *e = create_array_access("arr", create_const(-1));
    typechecker_infer(&tc, e);
    ASSERT_EQ(tc.error_count, 1); /* negative index */
    expr_free(e);
}

TEST(test_non_array_access_error) {
    TypeChecker tc;
    typechecker_init(&tc);
    TypeDesc int_t = {TYPE_INT, 0};
    typechecker_add_symbol(&tc, "x", int_t);

    Expr *e = create_array_access("x", create_const(0));
    typechecker_infer(&tc, e);
    ASSERT_TRUE(tc.error_count >= 1); /* not an array */
    expr_free(e);
}

/* === Full program type checking === */

TEST(test_check_simple_program) {
    TypeChecker tc;
    typechecker_init(&tc);

    const char *src = "int main() { int x = 1; int y = x + 2; return y; }";
    Expr *prog = parse_program(src);
    ASSERT_NOT_NULL(prog);

    int errs = typechecker_check(&tc, prog);
    ASSERT_EQ(errs, 0);
    expr_free(prog);
}

TEST(test_check_array_program) {
    TypeChecker tc;
    typechecker_init(&tc);

    const char *src = "int main() { int arr[3] = {1, 2, 3}; return arr[0]; }";
    Expr *prog = parse_program(src);
    ASSERT_NOT_NULL(prog);

    int errs = typechecker_check(&tc, prog);
    ASSERT_EQ(errs, 0);
    expr_free(prog);
}

TEST(test_too_many_initializers) {
    TypeChecker tc;
    typechecker_init(&tc);

    /* 4 init values for array of size 2 */
    Expr **inits = (Expr **)malloc(4 * sizeof(Expr *));
    inits[0] = create_const(1);
    inits[1] = create_const(2);
    inits[2] = create_const(3);
    inits[3] = create_const(4);
    Expr *decl = create_array_decl("arr", 2, inits, 4);

    Expr *prog = create_program();
    Expr *fn = create_func_def("main", NULL, 0, create_return(create_const(0)));
    /* Inject the array decl as a preceding statement */
    fn->param_count = 1;
    fn->params = (Expr **)malloc(sizeof(Expr *));
    fn->params[0] = decl;
    program_add_func(prog, fn);

    int errs = typechecker_check(&tc, prog);
    ASSERT_TRUE(errs >= 1); /* too many initializers */
    expr_free(prog);
}

int main(void) {
    TEST_SUITE_BEGIN("TypeChecker");

    RUN_TEST(test_const_is_int);
    RUN_TEST(test_var_declared);
    RUN_TEST(test_var_undeclared);
    RUN_TEST(test_binop_int);
    RUN_TEST(test_comparison_returns_int);
    RUN_TEST(test_addr_of_returns_ptr);
    RUN_TEST(test_deref_ptr);
    RUN_TEST(test_deref_non_ptr_error);
    RUN_TEST(test_array_access_valid);
    RUN_TEST(test_array_bounds_error);
    RUN_TEST(test_array_negative_index_error);
    RUN_TEST(test_non_array_access_error);
    RUN_TEST(test_check_simple_program);
    RUN_TEST(test_check_array_program);
    RUN_TEST(test_too_many_initializers);

    TEST_SUITE_END();
}
