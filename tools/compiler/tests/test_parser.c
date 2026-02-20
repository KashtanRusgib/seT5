/*
 * test_parser.c - Unit tests for the recursive descent function parser
 *
 * Tests: parse_program() from parser.c
 * Coverage: simple function, return statement, parameters, function calls,
 *           multiple functions, error handling, operator precedence
 */

#include "../include/test_harness.h"
#include "../include/parser.h"
#include "../include/ir.h"

/* ---- Parse simple main() ---- */

TEST(test_parse_simple_main) {
    Expr *prog = parse_program("int main() { return 42; }");
    ASSERT_NOT_NULL(prog);
    ASSERT_EQ(prog->type, NODE_PROGRAM);
    ASSERT_EQ(prog->param_count, 1);

    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->type, NODE_FUNC_DEF);
    ASSERT_STR_EQ(fn->name, "main");
    ASSERT_EQ(fn->param_count, 0);

    Expr *body = fn->body;
    ASSERT_NOT_NULL(body);
    ASSERT_EQ(body->type, NODE_RETURN);
    ASSERT_NOT_NULL(body->left);
    ASSERT_EQ(body->left->type, NODE_CONST);
    ASSERT_EQ(body->left->val, 42);

    expr_free(prog);
}

/* ---- Parse return with arithmetic expression ---- */

TEST(test_parse_return_expr) {
    Expr *prog = parse_program("int main() { return 1 + 2; }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    Expr *ret = fn->body;
    ASSERT_EQ(ret->type, NODE_RETURN);

    Expr *expr = ret->left;
    ASSERT_EQ(expr->type, NODE_BINOP);
    ASSERT_EQ(expr->op, OP_IR_ADD);
    ASSERT_EQ(expr->left->type, NODE_CONST);
    ASSERT_EQ(expr->left->val, 1);
    ASSERT_EQ(expr->right->type, NODE_CONST);
    ASSERT_EQ(expr->right->val, 2);

    expr_free(prog);
}

/* ---- Parse function with parameter ---- */

TEST(test_parse_func_with_param) {
    Expr *prog = parse_program("int foo(int x) { return x; }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->type, NODE_FUNC_DEF);
    ASSERT_STR_EQ(fn->name, "foo");
    ASSERT_EQ(fn->param_count, 1);
    ASSERT_EQ(fn->params[0]->type, NODE_VAR);
    ASSERT_STR_EQ(fn->params[0]->name, "x");

    Expr *ret = fn->body;
    ASSERT_EQ(ret->type, NODE_RETURN);
    ASSERT_EQ(ret->left->type, NODE_VAR);
    ASSERT_STR_EQ(ret->left->name, "x");

    expr_free(prog);
}

/* ---- Parse function call ---- */

TEST(test_parse_func_call) {
    Expr *prog = parse_program("int main() { return foo(5); }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    Expr *ret = fn->body;
    ASSERT_EQ(ret->type, NODE_RETURN);

    Expr *call = ret->left;
    ASSERT_EQ(call->type, NODE_FUNC_CALL);
    ASSERT_STR_EQ(call->name, "foo");
    ASSERT_EQ(call->param_count, 1);
    ASSERT_EQ(call->params[0]->type, NODE_CONST);
    ASSERT_EQ(call->params[0]->val, 5);

    expr_free(prog);
}

/* ---- Parse multiple functions ---- */

TEST(test_parse_multi_func) {
    Expr *prog = parse_program(
        "int foo(int x) { return x + 1; } "
        "int main() { return foo(5); }");
    ASSERT_NOT_NULL(prog);
    ASSERT_EQ(prog->type, NODE_PROGRAM);
    ASSERT_EQ(prog->param_count, 2);

    ASSERT_STR_EQ(prog->params[0]->name, "foo");
    ASSERT_STR_EQ(prog->params[1]->name, "main");

    /* foo's body: return x + 1 */
    Expr *foo_ret = prog->params[0]->body;
    ASSERT_EQ(foo_ret->type, NODE_RETURN);
    ASSERT_EQ(foo_ret->left->type, NODE_BINOP);
    ASSERT_EQ(foo_ret->left->op, OP_IR_ADD);

    /* main's body: return foo(5) */
    Expr *main_ret = prog->params[1]->body;
    ASSERT_EQ(main_ret->type, NODE_RETURN);
    ASSERT_EQ(main_ret->left->type, NODE_FUNC_CALL);
    ASSERT_STR_EQ(main_ret->left->name, "foo");

    expr_free(prog);
}

/* ---- Parse invalid function (missing closing paren) ---- */

TEST(test_parse_invalid_func) {
    Expr *prog = parse_program("int main( { return 42; }");
    ASSERT_NULL(prog);
}

/* ---- Parse return with operator precedence (* > +) ---- */

TEST(test_parse_return_precedence) {
    /* return 1 + 2 * 3; should parse as 1 + (2 * 3) */
    Expr *prog = parse_program("int main() { return 1 + 2 * 3; }");
    ASSERT_NOT_NULL(prog);

    Expr *ret = prog->params[0]->body;
    Expr *expr = ret->left;
    ASSERT_EQ(expr->type, NODE_BINOP);
    ASSERT_EQ(expr->op, OP_IR_ADD);

    /* Left is 1 */
    ASSERT_EQ(expr->left->type, NODE_CONST);
    ASSERT_EQ(expr->left->val, 1);

    /* Right is 2 * 3 */
    ASSERT_EQ(expr->right->type, NODE_BINOP);
    ASSERT_EQ(expr->right->op, OP_IR_MUL);
    ASSERT_EQ(expr->right->left->val, 2);
    ASSERT_EQ(expr->right->right->val, 3);

    expr_free(prog);
}

/* ====== Phase 3: Structured control flow parsing ====== */

/* ---- Parse if statement ---- */

TEST(test_parse_if_simple) {
    Expr *prog = parse_program(
        "int main() { if (1 == 1) { return 42; } return 0; }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->type, NODE_FUNC_DEF);

    /* The function body should be NODE_RETURN (the 'return 0;')
     * preceding stmts should contain the if */
    /* fn->params has the params + preceding stmts; body is the last stmt */
    /* With our parser, 'if' is a preceding stmt, 'return 0' is the body */
    ASSERT_TRUE(fn->param_count >= 1);

    /* Find the if node in the params (preceding stmts) */
    int found_if = 0;
    for (int i = 0; i < fn->param_count; i++) {
        if (fn->params[i]->type == NODE_IF) found_if = 1;
    }
    ASSERT_TRUE(found_if);

    expr_free(prog);
}

/* ---- Parse if-else ---- */

TEST(test_parse_if_else) {
    Expr *prog = parse_program(
        "int main() { if (1 < 2) { return 10; } else { return 20; } }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    /* The if-else is either the body or a preceding stmt */
    Expr *if_node = NULL;
    if (fn->body && fn->body->type == NODE_IF) {
        if_node = fn->body;
    } else {
        for (int i = 0; i < fn->param_count; i++) {
            if (fn->params[i]->type == NODE_IF) {
                if_node = fn->params[i];
                break;
            }
        }
    }
    ASSERT_NOT_NULL(if_node);
    ASSERT_NOT_NULL(if_node->condition);
    ASSERT_NOT_NULL(if_node->body);
    ASSERT_NOT_NULL(if_node->else_body);

    /* Condition should be 1 < 2 */
    ASSERT_EQ(if_node->condition->type, NODE_BINOP);
    ASSERT_EQ(if_node->condition->op, OP_IR_CMP_LT);

    expr_free(prog);
}

/* ---- Parse while loop ---- */

TEST(test_parse_while) {
    Expr *prog = parse_program(
        "int main() { int x = 10; while (x > 0) { x = x - 1; } return x; }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    /* Find the while node */
    int found_while = 0;
    for (int i = 0; i < fn->param_count; i++) {
        if (fn->params[i]->type == NODE_WHILE) {
            found_while = 1;
            ASSERT_NOT_NULL(fn->params[i]->condition);
            ASSERT_NOT_NULL(fn->params[i]->body);
        }
    }
    ASSERT_TRUE(found_while);

    expr_free(prog);
}

/* ---- Parse for loop ---- */

TEST(test_parse_for) {
    Expr *prog = parse_program(
        "int main() { int sum = 0; for (int i = 0; i < 5; i++) { sum = sum + i; } return sum; }");
    ASSERT_NOT_NULL(prog);

    Expr *fn = prog->params[0];
    int found_for = 0;
    for (int i = 0; i < fn->param_count; i++) {
        if (fn->params[i]->type == NODE_FOR) {
            found_for = 1;
            ASSERT_NOT_NULL(fn->params[i]->condition);
            ASSERT_NOT_NULL(fn->params[i]->body);
            ASSERT_NOT_NULL(fn->params[i]->increment);
        }
    }
    ASSERT_TRUE(found_for);

    expr_free(prog);
}

/* ---- Parse comparison operators ---- */

TEST(test_parse_comparison_eq) {
    Expr *prog = parse_program("int main() { return 5 == 5; }");
    ASSERT_NOT_NULL(prog);

    Expr *ret = prog->params[0]->body;
    ASSERT_EQ(ret->type, NODE_RETURN);
    ASSERT_EQ(ret->left->type, NODE_BINOP);
    ASSERT_EQ(ret->left->op, OP_IR_CMP_EQ);

    expr_free(prog);
}

TEST(test_parse_comparison_lt) {
    Expr *prog = parse_program("int main() { return 3 < 5; }");
    ASSERT_NOT_NULL(prog);

    Expr *ret = prog->params[0]->body;
    ASSERT_EQ(ret->left->type, NODE_BINOP);
    ASSERT_EQ(ret->left->op, OP_IR_CMP_LT);

    expr_free(prog);
}

TEST(test_parse_comparison_gt) {
    Expr *prog = parse_program("int main() { return 10 > 3; }");
    ASSERT_NOT_NULL(prog);

    Expr *ret = prog->params[0]->body;
    ASSERT_EQ(ret->left->type, NODE_BINOP);
    ASSERT_EQ(ret->left->op, OP_IR_CMP_GT);

    expr_free(prog);
}

int main(void) {
    TEST_SUITE_BEGIN("Parser (Functions)");

    RUN_TEST(test_parse_simple_main);
    RUN_TEST(test_parse_return_expr);
    RUN_TEST(test_parse_func_with_param);
    RUN_TEST(test_parse_func_call);
    RUN_TEST(test_parse_multi_func);
    RUN_TEST(test_parse_invalid_func);
    RUN_TEST(test_parse_return_precedence);

    /* Phase 3: Control flow parsing */
    RUN_TEST(test_parse_if_simple);
    RUN_TEST(test_parse_if_else);
    RUN_TEST(test_parse_while);
    RUN_TEST(test_parse_for);
    RUN_TEST(test_parse_comparison_eq);
    RUN_TEST(test_parse_comparison_lt);
    RUN_TEST(test_parse_comparison_gt);

    TEST_SUITE_END();
}
