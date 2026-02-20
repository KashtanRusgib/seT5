/*
 * test_memory.c - Tests for TASK-015: Pointers and Memory Model
 *
 * Tests: ternary addressing, VM load/store, pointer IR nodes,
 * parser pointer syntax, memory read/write through trit addresses.
 */

#include "../include/test_harness.h"
#include "../include/ternary.h"
#include "../include/memory.h"
#include "../include/vm.h"
#include "../include/ir.h"
#include "../include/parser.h"

/* ---- Ternary address conversion ---- */

TEST(test_addr_zero) {
    trit_addr addr;
    int_to_trit_word(0, addr);
    int idx = trit_addr_to_index(addr);
    ASSERT_EQ(idx, MEMORY_SIZE / 2);
}

TEST(test_addr_positive) {
    trit_addr addr;
    int_to_trit_word(1, addr);
    int idx = trit_addr_to_index(addr);
    ASSERT_EQ(idx, MEMORY_SIZE / 2 + 1);
}

TEST(test_addr_negative) {
    trit_addr addr;
    int_to_trit_word(-1, addr);
    int idx = trit_addr_to_index(addr);
    ASSERT_EQ(idx, MEMORY_SIZE / 2 - 1);
}

TEST(test_addr_roundtrip) {
    trit_addr addr, addr2;
    int_to_trit_word(42, addr);
    int idx = trit_addr_to_index(addr);
    index_to_trit_addr(idx, addr2);
    ASSERT_EQ(trit_word_to_int(addr), trit_word_to_int(addr2));
}

/* ---- Ternary memory read/write ---- */

TEST(test_tmem_write_read) {
    vm_memory_reset();
    trit_addr addr;
    int_to_trit_word(5, addr);
    tmem_write(addr, 99);
    ASSERT_EQ(tmem_read(addr), 99);
}

TEST(test_tmem_zero_addr) {
    vm_memory_reset();
    trit_addr addr;
    int_to_trit_word(0, addr);
    tmem_write(addr, -7);
    ASSERT_EQ(tmem_read(addr), -7);
}

TEST(test_tmem_negative_addr) {
    vm_memory_reset();
    trit_addr addr;
    int_to_trit_word(-10, addr);
    tmem_write(addr, 123);
    ASSERT_EQ(tmem_read(addr), 123);
}

/* ---- VM LOAD/STORE opcodes ---- */

TEST(test_vm_store_load) {
    vm_memory_reset();
    /* PUSH 10 (addr), PUSH 42 (value), STORE, PUSH 10, LOAD, HALT */
    unsigned char prog[] = {
        OP_PUSH, 10,
        OP_PUSH, 42,
        OP_STORE,
        OP_PUSH, 10,
        OP_LOAD,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* After HALT, result printed is the loaded value = 42 */
    ASSERT_EQ(vm_memory_read(10), 42);
}

TEST(test_vm_store_multiple) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 0, OP_PUSH, 11, OP_STORE,
        OP_PUSH, 1, OP_PUSH, 22, OP_STORE,
        OP_PUSH, 2, OP_PUSH, 33, OP_STORE,
        OP_PUSH, 1, OP_LOAD,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    ASSERT_EQ(vm_memory_read(0), 11);
    ASSERT_EQ(vm_memory_read(1), 22);
    ASSERT_EQ(vm_memory_read(2), 33);
}

TEST(test_vm_sub) {
    vm_memory_reset();
    unsigned char prog[] = {
        OP_PUSH, 10,
        OP_PUSH, 3,
        OP_SUB,
        OP_HALT
    };
    vm_run(prog, sizeof(prog));
    /* 10 - 3 = 7, printed by HALT */
}

/* ---- IR pointer nodes ---- */

TEST(test_ir_deref) {
    Expr *var = create_var("p");
    Expr *d = create_deref(var);
    ASSERT_NOT_NULL(d);
    ASSERT_EQ(d->type, NODE_DEREF);
    ASSERT_NOT_NULL(d->left);
    ASSERT_EQ(d->left->type, NODE_VAR);
    expr_free(d);
}

TEST(test_ir_addr_of) {
    Expr *var = create_var("x");
    Expr *a = create_addr_of(var);
    ASSERT_NOT_NULL(a);
    ASSERT_EQ(a->type, NODE_ADDR_OF);
    ASSERT_NOT_NULL(a->left);
    ASSERT_EQ(a->left->type, NODE_VAR);
    expr_free(a);
}

TEST(test_ir_assign) {
    Expr *lhs = create_var("x");
    Expr *rhs = create_const(5);
    Expr *a = create_assign(lhs, rhs);
    ASSERT_NOT_NULL(a);
    ASSERT_EQ(a->type, NODE_ASSIGN);
    ASSERT_EQ(a->left->type, NODE_VAR);
    ASSERT_EQ(a->right->type, NODE_CONST);
    ASSERT_EQ(a->right->val, 5);
    expr_free(a);
}

TEST(test_ir_var_decl) {
    Expr *init = create_const(42);
    Expr *d = create_var_decl("count", init);
    ASSERT_NOT_NULL(d);
    ASSERT_EQ(d->type, NODE_VAR_DECL);
    ASSERT_STR_EQ(d->name, "count");
    ASSERT_EQ(d->left->type, NODE_CONST);
    ASSERT_EQ(d->left->val, 42);
    expr_free(d);
}

/* ---- Parser pointer syntax ---- */

TEST(test_parse_var_decl) {
    Expr *prog = parse_program("int main() { int x = 5; return x; }");
    ASSERT_NOT_NULL(prog);
    ASSERT_EQ(prog->type, NODE_PROGRAM);
    ASSERT_EQ(prog->param_count, 1); /* one function */
    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->type, NODE_FUNC_DEF);
    /* body is 'return x', param list includes 'int x = 5' decl */
    ASSERT_EQ(fn->body->type, NODE_RETURN);
    expr_free(prog);
}

TEST(test_parse_addr_of) {
    Expr *prog = parse_program("int main() { return &x; }");
    /* Won't fail even though &x has no meaning without a symbol table,
     * but it parses correctly. Note: 'x' is referenced without declaration
     * which is allowed in the parser (semantic checking is Phase 3). */
    /* Actually: &x requires x to be an ident. Check parse works. */
    /* The parser expects a primary starting with TOK_AMP then TOK_IDENT.
     * But 'x' is undeclared — the parser doesn't care, it just builds AST. */
    ASSERT_NOT_NULL(prog);
    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->body->type, NODE_RETURN);
    ASSERT_EQ(fn->body->left->type, NODE_ADDR_OF);
    expr_free(prog);
}

TEST(test_parse_deref) {
    Expr *prog = parse_program("int main() { return *p; }");
    ASSERT_NOT_NULL(prog);
    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->body->type, NODE_RETURN);
    ASSERT_EQ(fn->body->left->type, NODE_DEREF);
    expr_free(prog);
}

TEST(test_parse_subtraction) {
    Expr *prog = parse_program("int main() { return 10 - 3; }");
    ASSERT_NOT_NULL(prog);
    Expr *fn = prog->params[0];
    ASSERT_EQ(fn->body->type, NODE_RETURN);
    /* parse_program doesn't call optimize, so 10-3 stays as BINOP */
    ASSERT_EQ(fn->body->left->type, NODE_BINOP);
    ASSERT_EQ(fn->body->left->op, OP_IR_SUB);
    expr_free(prog);
}

TEST(test_fold_subtraction) {
    Expr *e = create_binop(OP_IR_SUB, create_const(10), create_const(3));
    optimize(e);
    ASSERT_EQ(e->type, NODE_CONST);
    ASSERT_EQ(e->val, 7);
    expr_free(e);
}

int main(void) {
    TEST_SUITE_BEGIN("Memory Model (TASK-015)");
    /* Ternary address tests */
    RUN_TEST(test_addr_zero);
    RUN_TEST(test_addr_positive);
    RUN_TEST(test_addr_negative);
    RUN_TEST(test_addr_roundtrip);
    /* Ternary memory tests */
    RUN_TEST(test_tmem_write_read);
    RUN_TEST(test_tmem_zero_addr);
    RUN_TEST(test_tmem_negative_addr);
    /* VM memory ops */
    RUN_TEST(test_vm_store_load);
    RUN_TEST(test_vm_store_multiple);
    RUN_TEST(test_vm_sub);
    /* IR pointer nodes */
    RUN_TEST(test_ir_deref);
    RUN_TEST(test_ir_addr_of);
    RUN_TEST(test_ir_assign);
    RUN_TEST(test_ir_var_decl);
    /* Parser pointer syntax */
    RUN_TEST(test_parse_var_decl);
    RUN_TEST(test_parse_addr_of);
    RUN_TEST(test_parse_deref);
    RUN_TEST(test_parse_subtraction);
    RUN_TEST(test_fold_subtraction);
    TEST_SUITE_END();
}
