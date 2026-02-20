/*
 * test_bootstrap.c - Tests for TASK-018: Self-Hosting Bootstrap
 *
 * Tests: symbol table, AST-to-bytecode emission, bootstrap compile,
 * self-test (compile & run mini-program), variable support.
 */

#include "../include/test_harness.h"
#include "../include/bootstrap.h"
#include "../include/vm.h"
#include "../include/ir.h"

/* ---- Symbol table tests ---- */

TEST(test_symtab_init) {
    BootstrapSymTab tab;
    symtab_init(&tab);
    ASSERT_EQ(tab.count, 0);
    ASSERT_EQ(tab.next_offset, 0);
}

TEST(test_symtab_add) {
    BootstrapSymTab tab;
    symtab_init(&tab);
    int off = symtab_add(&tab, "x", 0);
    ASSERT_EQ(off, 0);
    ASSERT_EQ(tab.count, 1);
    int off2 = symtab_add(&tab, "y", 1);
    ASSERT_EQ(off2, 1);
    ASSERT_EQ(tab.count, 2);
}

TEST(test_symtab_lookup) {
    BootstrapSymTab tab;
    symtab_init(&tab);
    symtab_add(&tab, "alpha", 0);
    symtab_add(&tab, "beta", 0);
    ASSERT_EQ(symtab_lookup(&tab, "alpha"), 0);
    ASSERT_EQ(symtab_lookup(&tab, "beta"), 1);
    ASSERT_EQ(symtab_lookup(&tab, "gamma"), -1);
}

TEST(test_symtab_full) {
    BootstrapSymTab tab;
    symtab_init(&tab);
    /* Fill up symbol table */
    for (int i = 0; i < MAX_SYMBOLS; i++) {
        char name[8];
        snprintf(name, sizeof(name), "v%d", i);
        ASSERT_TRUE(symtab_add(&tab, name, 0) >= 0);
    }
    /* Next add should fail */
    ASSERT_EQ(symtab_add(&tab, "overflow", 0), -1);
}

/* ---- Bootstrap compile tests ---- */

TEST(test_bootstrap_simple_const) {
    unsigned char code[256];
    int len = bootstrap_compile("int main() { return 42; }", code, 256);
    ASSERT_TRUE(len > 0);
    /* Should contain at least OP_PUSH, 42, OP_HALT */
    ASSERT_TRUE(len >= 3);
}

TEST(test_bootstrap_addition) {
    unsigned char code[256];
    int len = bootstrap_compile("int main() { return 1 + 2; }", code, 256);
    ASSERT_TRUE(len > 0);
    /* Constant folding: 1+2=3, so should be PUSH 3, HALT */
    /* Actually, optimize is called, so it should fold. */
    ASSERT_TRUE(len >= 3);
}

TEST(test_bootstrap_var_decl) {
    unsigned char code[256];
    int len = bootstrap_compile("int main() { int x = 5; return x; }", code, 256);
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_multi_var) {
    unsigned char code[256];
    int len = bootstrap_compile(
        "int main() { int a = 1 + 2; int b = a * 3; return b; }",
        code, 256
    );
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_self_test) {
    int result = bootstrap_self_test();
    ASSERT_EQ(result, 0);
}

TEST(test_bootstrap_subtraction) {
    unsigned char code[256];
    int len = bootstrap_compile("int main() { return 10 - 3; }", code, 256);
    ASSERT_TRUE(len > 0);
    /* After constant folding: 10-3=7, so PUSH 7, HALT */
}

TEST(test_bootstrap_nested_expr) {
    unsigned char code[256];
    int len = bootstrap_compile(
        "int main() { int x = 2 * 3 + 1; return x; }",
        code, 256
    );
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_pointer_syntax) {
    unsigned char code[256];
    int len = bootstrap_compile(
        "int main() { int x = 10; return &x; }",
        code, 256
    );
    /* Should parse and compile, even if address-of is simple */
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_roundtrip) {
    /* Round-trip test: compile same source twice, verify identical bytecode */
    const char *src = "int main() { int a = 2 + 3; return a * a; }";
    unsigned char code1[256], code2[256];
    int len1 = bootstrap_compile(src, code1, 256);
    int len2 = bootstrap_compile(src, code2, 256);
    ASSERT_TRUE(len1 > 0);
    ASSERT_EQ(len1, len2);
    for (int i = 0; i < len1; i++) {
        ASSERT_EQ(code1[i], code2[i]);
    }
}

TEST(test_bootstrap_error_handling) {
    /* Empty source should still produce something (empty program) or fail gracefully */
    unsigned char code[256];
    int len = bootstrap_compile("", code, 256);
    /* Either returns >0 (empty program with HALT) or -1 (parse error) — both are valid */
    ASSERT_TRUE(len == -1 || len > 0);
}

/* ====== Phase 3: Control flow compilation tests ====== */

TEST(test_bootstrap_if_simple) {
    /* if (1 == 1) { return 42; } return 0; */
    unsigned char code[512];
    int len = bootstrap_compile(
        "int main() { if (1 == 1) { return 42; } return 0; }",
        code, 512);
    ASSERT_TRUE(len > 0);
    /* Should compile without errors */
}

TEST(test_bootstrap_if_else) {
    unsigned char code[512];
    int len = bootstrap_compile(
        "int main() { if (1 < 2) { return 10; } else { return 20; } }",
        code, 512);
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_while_loop) {
    unsigned char code[512];
    int len = bootstrap_compile(
        "int main() { int x = 5; while (x > 0) { x = x - 1; } return x; }",
        code, 512);
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_for_loop) {
    unsigned char code[512];
    int len = bootstrap_compile(
        "int main() { int sum = 0; for (int i = 0; i < 5; i++) { sum = sum + i; } return sum; }",
        code, 512);
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_comparison_eq) {
    unsigned char code[256];
    int len = bootstrap_compile(
        "int main() { return 5 == 5; }",
        code, 256);
    ASSERT_TRUE(len > 0);
    /* After constant folding, 5==5 -> 1, so PUSH 1, HALT */
}

TEST(test_bootstrap_comparison_ops) {
    unsigned char code[256];
    int len;

    len = bootstrap_compile("int main() { return 3 < 5; }", code, 256);
    ASSERT_TRUE(len > 0);

    len = bootstrap_compile("int main() { return 10 > 3; }", code, 256);
    ASSERT_TRUE(len > 0);
}

TEST(test_bootstrap_nested_if) {
    unsigned char code[512];
    int len = bootstrap_compile(
        "int main() { int x = 10; "
        "if (x > 5) { if (x > 8) { return 1; } return 2; } "
        "return 3; }",
        code, 512);
    ASSERT_TRUE(len > 0);
}

int main(void) {
    TEST_SUITE_BEGIN("Bootstrap Self-Host (TASK-018)");
    /* Symbol table */
    RUN_TEST(test_symtab_init);
    RUN_TEST(test_symtab_add);
    RUN_TEST(test_symtab_lookup);
    RUN_TEST(test_symtab_full);
    /* Compilation */
    RUN_TEST(test_bootstrap_simple_const);
    RUN_TEST(test_bootstrap_addition);
    RUN_TEST(test_bootstrap_var_decl);
    RUN_TEST(test_bootstrap_multi_var);
    RUN_TEST(test_bootstrap_subtraction);
    RUN_TEST(test_bootstrap_nested_expr);
    RUN_TEST(test_bootstrap_pointer_syntax);
    RUN_TEST(test_bootstrap_roundtrip);
    RUN_TEST(test_bootstrap_error_handling);
    /* Phase 3: Control flow */
    RUN_TEST(test_bootstrap_if_simple);
    RUN_TEST(test_bootstrap_if_else);
    RUN_TEST(test_bootstrap_while_loop);
    RUN_TEST(test_bootstrap_for_loop);
    RUN_TEST(test_bootstrap_comparison_eq);
    RUN_TEST(test_bootstrap_comparison_ops);
    RUN_TEST(test_bootstrap_nested_if);
    /* Self-test */
    RUN_TEST(test_bootstrap_self_test);
    TEST_SUITE_END();
}
