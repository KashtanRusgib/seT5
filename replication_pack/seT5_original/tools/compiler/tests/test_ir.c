/*
 * test_ir.c - Unit tests for the IR and constant folding optimizer
 *
 * Tests: create_const, create_var, create_binop, optimize, expr_free
 * Coverage: folding add, folding mul, nested fold, no-fold with vars,
 *           single const passthrough, chained operations
 */

#include "../include/test_harness.h"
#include "../include/ir.h"

/* ---- Constant folding: addition ---- */

TEST(test_fold_add) {
    /* 1 + 2 = 3 */
    Expr *e = create_binop(OP_IR_ADD, create_const(1), create_const(2));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 3);
    expr_free(e);
}

/* ---- Constant folding: multiplication ---- */

TEST(test_fold_mul) {
    /* 3 * 4 = 12 */
    Expr *e = create_binop(OP_IR_MUL, create_const(3), create_const(4));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 12);
    expr_free(e);
}

/* ---- No fold when variable present ---- */

TEST(test_no_fold_vars) {
    /* x + 2 should NOT fold */
    Expr *e = create_binop(OP_IR_ADD, create_var("x"), create_const(2));
    optimize(e);
    ASSERT_EQ(e->type, NODE_BINOP);
    ASSERT_EQ(e->left->type, NODE_VAR);
    ASSERT_EQ(e->right->type, NODE_CONST);
    ASSERT_EQ(e->right->val, 2);
    expr_free(e);
}

/* ---- Nested constant folding ---- */

TEST(test_fold_nested) {
    /* (1 + 2) * (3 + 4) = 3 * 7 = 21 */
    Expr *left = create_binop(OP_IR_ADD, create_const(1), create_const(2));
    Expr *right = create_binop(OP_IR_ADD, create_const(3), create_const(4));
    Expr *e = create_binop(OP_IR_MUL, left, right);
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 21);
    expr_free(e);
}

/* ---- Partial fold: one branch foldable ---- */

TEST(test_fold_partial) {
    /* (1 + 2) * x -> 3 * x (partial: left folds, top stays binop) */
    Expr *left = create_binop(OP_IR_ADD, create_const(1), create_const(2));
    Expr *e = create_binop(OP_IR_MUL, left, create_var("x"));
    optimize(e);
    ASSERT_EQ(e->type, NODE_BINOP);
    ASSERT_EQ(e->left->type, NODE_CONST);
    ASSERT_EQ(e->left->val, 3);
    ASSERT_EQ(e->right->type, NODE_VAR);
    expr_free(e);
}

/* ---- Single constant: no-op optimize ---- */

TEST(test_single_const) {
    Expr *e = create_const(42);
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 42);
    expr_free(e);
}

/* ---- Single var: no-op optimize ---- */

TEST(test_single_var) {
    Expr *e = create_var("y");
    optimize(e);
    ASSERT_EQ(e->type, NODE_VAR);
    expr_free(e);
}

/* ---- Fold with zero ---- */

TEST(test_fold_add_zero) {
    /* 0 + 5 = 5 */
    Expr *e = create_binop(OP_IR_ADD, create_const(0), create_const(5));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 5);
    expr_free(e);
}

TEST(test_fold_mul_zero) {
    /* 7 * 0 = 0 */
    Expr *e = create_binop(OP_IR_MUL, create_const(7), create_const(0));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 0);
    expr_free(e);
}

/* ---- Deeply nested chain ---- */

TEST(test_fold_deep_chain) {
    /* ((2 * 3) + (4 * 5)) + 1 = (6 + 20) + 1 = 27 */
    Expr *a = create_binop(OP_IR_MUL, create_const(2), create_const(3));
    Expr *b = create_binop(OP_IR_MUL, create_const(4), create_const(5));
    Expr *c = create_binop(OP_IR_ADD, a, b);
    Expr *e = create_binop(OP_IR_ADD, c, create_const(1));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 27);
    expr_free(e);
}

/* ---- NULL safety ---- */

TEST(test_optimize_null) {
    /* Should not crash */
    optimize(NULL);
    ASSERT_TRUE(1);
}

/* ====== Phase 3: Comparison folding ====== */

TEST(test_fold_cmp_eq_true) {
    /* 5 == 5 -> 1 */
    Expr *e = create_binop(OP_IR_CMP_EQ, create_const(5), create_const(5));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 1);
    expr_free(e);
}

TEST(test_fold_cmp_eq_false) {
    /* 5 == 3 -> 0 */
    Expr *e = create_binop(OP_IR_CMP_EQ, create_const(5), create_const(3));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 0);
    expr_free(e);
}

TEST(test_fold_cmp_lt) {
    /* 3 < 5 -> 1 */
    Expr *e = create_binop(OP_IR_CMP_LT, create_const(3), create_const(5));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 1);
    expr_free(e);
}

TEST(test_fold_cmp_gt) {
    /* 10 > 3 -> 1 */
    Expr *e = create_binop(OP_IR_CMP_GT, create_const(10), create_const(3));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 1);
    expr_free(e);
}

/* ====== Phase 3: Control flow node creation ====== */

TEST(test_create_if) {
    Expr *cond = create_binop(OP_IR_CMP_EQ, create_const(1), create_const(1));
    Expr *body = create_return(create_const(42));
    Expr *e = create_if(cond, body, NULL);
    ASSERT_EQ(e->type, NODE_IF);
    ASSERT_NOT_NULL(e->condition);
    ASSERT_NOT_NULL(e->body);
    ASSERT_NULL(e->else_body);
    expr_free(e);
}

TEST(test_create_if_else) {
    Expr *cond = create_binop(OP_IR_CMP_LT, create_const(1), create_const(2));
    Expr *body = create_return(create_const(10));
    Expr *else_body = create_return(create_const(20));
    Expr *e = create_if(cond, body, else_body);
    ASSERT_EQ(e->type, NODE_IF);
    ASSERT_NOT_NULL(e->else_body);
    expr_free(e);
}

TEST(test_create_while) {
    Expr *cond = create_binop(OP_IR_CMP_GT, create_var("x"), create_const(0));
    Expr *body = create_assign(create_var("x"),
        create_binop(OP_IR_SUB, create_var("x"), create_const(1)));
    Expr *e = create_while(cond, body);
    ASSERT_EQ(e->type, NODE_WHILE);
    ASSERT_NOT_NULL(e->condition);
    ASSERT_NOT_NULL(e->body);
    expr_free(e);
}

TEST(test_create_for) {
    Expr *init = create_var_decl("i", create_const(0));
    Expr *cond = create_binop(OP_IR_CMP_LT, create_var("i"), create_const(10));
    Expr *inc = create_assign(create_var("i"),
        create_binop(OP_IR_ADD, create_var("i"), create_const(1)));
    Expr *body = create_return(create_var("i"));
    Expr *e = create_for(init, cond, inc, body);
    ASSERT_EQ(e->type, NODE_FOR);
    ASSERT_NOT_NULL(e->condition);
    ASSERT_NOT_NULL(e->increment);
    ASSERT_NOT_NULL(e->body);
    ASSERT_NOT_NULL(e->left);  /* init */
    expr_free(e);
}

TEST(test_create_block) {
    Expr *block = create_block();
    ASSERT_EQ(block->type, NODE_BLOCK);
    ASSERT_EQ(block->param_count, 0);

    block_add_stmt(block, create_const(1));
    block_add_stmt(block, create_const(2));
    ASSERT_EQ(block->param_count, 2);

    expr_free(block);
}

int main(void) {
    TEST_SUITE_BEGIN("IR / Constant Folding");

    RUN_TEST(test_fold_add);
    RUN_TEST(test_fold_mul);
    RUN_TEST(test_no_fold_vars);
    RUN_TEST(test_fold_nested);
    RUN_TEST(test_fold_partial);
    RUN_TEST(test_single_const);
    RUN_TEST(test_single_var);
    RUN_TEST(test_fold_add_zero);
    RUN_TEST(test_fold_mul_zero);
    RUN_TEST(test_fold_deep_chain);
    RUN_TEST(test_optimize_null);

    /* Phase 3: Comparison constant folding */
    RUN_TEST(test_fold_cmp_eq_true);
    RUN_TEST(test_fold_cmp_eq_false);
    RUN_TEST(test_fold_cmp_lt);
    RUN_TEST(test_fold_cmp_gt);

    /* Phase 3: Control flow node creation */
    RUN_TEST(test_create_if);
    RUN_TEST(test_create_if_else);
    RUN_TEST(test_create_while);
    RUN_TEST(test_create_for);
    RUN_TEST(test_create_block);

    TEST_SUITE_END();
}
