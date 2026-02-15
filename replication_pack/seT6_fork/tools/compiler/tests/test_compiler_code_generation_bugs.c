/* tools/compiler/tests/test_compiler_code_generation_bugs.c - Compiler code generation bug tests */
#include <stdio.h>
#include <assert.h>
#include "../include/test_harness.h"
#include "../include/ternary.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"

TEST(test_arithmetic_expression_codegen) {
    printf("Testing arithmetic expression code generation...\n");

    // Test complex arithmetic expressions
    tokenize("1 + 2 * 3 - 4 / 2");
    parse();
    codegen();

    // Verify bytecode generation
    ASSERT_GT(bc_idx, 0);
    ASSERT_EQ(bytecode[bc_idx - 1], OP_HALT);

    // Run and verify result
    vm_run(bytecode, bc_idx);
    // Expected: ((1 + 2) * 3) - (4 / 2) = 5 * 3 - 2 = 15 - 2 = 13
    // But depending on precedence: 1 + (2 * 3) - (4 / 2) = 1 + 6 - 2 = 5
    ASSERT_EQ(vm_result, 5);
}

TEST(test_variable_assignment_codegen) {
    printf("Testing variable assignment code generation...\n");

    tokenize("int x = 5; int y = x + 3;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    // Should execute without errors
    ASSERT_TRUE(vm_result >= 0);
}

TEST(test_control_flow_codegen) {
    printf("Testing control flow code generation...\n");

    tokenize("if (1) { return 42; } else { return 24; }");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 42);
}

TEST(test_function_call_codegen) {
    printf("Testing function call code generation...\n");

    tokenize("int func() { return 100; } int main() { return func(); }");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 100);
}

TEST(test_array_access_codegen) {
    printf("Testing array access code generation...\n");

    tokenize("int arr[5]; arr[0] = 10; return arr[0];");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 10);
}

TEST(test_pointer_operations_codegen) {
    printf("Testing pointer operations code generation...\n");

    tokenize("int x = 5; int *p = &x; return *p;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 5);
}

TEST(test_type_conversion_codegen) {
    printf("Testing type conversion code generation...\n");

    tokenize("float f = 3.14; int i = (int)f; return i;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 3);
}

TEST(test_ternary_operator_codegen) {
    printf("Testing ternary operator code generation...\n");

    tokenize("int x = 1 ? 10 : 20; return x;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 10);
}

TEST(test_loop_constructs_codegen) {
    printf("Testing loop constructs code generation...\n");

    tokenize("int sum = 0; for (int i = 0; i < 5; i++) { sum += i; } return sum;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 10); // 0+1+2+3+4 = 10
}

TEST(test_switch_statement_codegen) {
    printf("Testing switch statement code generation...\n");

    tokenize("int x = 2; switch(x) { case 1: return 10; case 2: return 20; default: return 30; }");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 20);
}

TEST(test_exception_handling_codegen) {
    printf("Testing exception handling code generation...\n");

    tokenize("try { throw 42; } catch(int e) { return e; }");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 42);
}

TEST(test_memory_management_codegen) {
    printf("Testing memory management code generation...\n");

    tokenize("int *p = new int(5); int val = *p; delete p; return val;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 5);
}

TEST(test_template_instantiation_codegen) {
    printf("Testing template instantiation code generation...\n");

    tokenize("template<typename T> T add(T a, T b) { return a + b; } int result = add<int>(3, 4); return result;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 7);
}

TEST(test_lambda_expression_codegen) {
    printf("Testing lambda expression code generation...\n");

    tokenize("auto lambda = [](int x) { return x * 2; }; return lambda(5);");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 10);
}

TEST(test_coroutine_codegen) {
    printf("Testing coroutine code generation...\n");

    tokenize("generator<int> fib() { int a = 0, b = 1; while (true) { co_yield a; int temp = a; a = b; b += temp; } } auto gen = fib(); return gen.next();");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 0); // First Fibonacci number
}

TEST(test_constexpr_codegen) {
    printf("Testing constexpr code generation...\n");

    tokenize("constexpr int factorial(int n) { return n <= 1 ? 1 : n * factorial(n-1); } int result = factorial(5); return result;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 120); // 5! = 120
}

TEST(test_optimization_bug_detection) {
    printf("Testing optimization bug detection...\n");

    // Test that optimizations don't break semantics
    tokenize("int x = 0; for (int i = 0; i < 10; i++) { x += 1; } return x;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 10);
}

TEST(test_codegen_edge_cases) {
    printf("Testing code generation edge cases...\n");

    // Empty function
    tokenize("void empty() {} int main() { empty(); return 0; }");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);

    vm_run(bytecode, bc_idx);
    ASSERT_EQ(vm_result, 0);
}

TEST(test_codegen_error_recovery) {
    printf("Testing code generation error recovery...\n");

    // Invalid code that should be handled gracefully
    tokenize("int x = ;"); // Syntax error
    int parse_result = parse();
    ASSERT_EQ(parse_result, -1); // Should fail parsing

    // Valid recovery
    tokenize("int x = 5;");
    parse();
    codegen();

    ASSERT_GT(bc_idx, 0);
}

int main(void) {
    TEST_SUITE_BEGIN("Compiler Code Generation Bugs");

    RUN_TEST(test_arithmetic_expression_codegen);
    RUN_TEST(test_variable_assignment_codegen);
    RUN_TEST(test_control_flow_codegen);
    RUN_TEST(test_function_call_codegen);
    RUN_TEST(test_array_access_codegen);
    RUN_TEST(test_pointer_operations_codegen);
    RUN_TEST(test_type_conversion_codegen);
    RUN_TEST(test_ternary_operator_codegen);
    RUN_TEST(test_loop_constructs_codegen);
    RUN_TEST(test_switch_statement_codegen);
    RUN_TEST(test_exception_handling_codegen);
    RUN_TEST(test_memory_management_codegen);
    RUN_TEST(test_template_instantiation_codegen);
    RUN_TEST(test_lambda_expression_codegen);
    RUN_TEST(test_coroutine_codegen);
    RUN_TEST(test_constexpr_codegen);
    RUN_TEST(test_optimization_bug_detection);
    RUN_TEST(test_codegen_edge_cases);
    RUN_TEST(test_codegen_error_recovery);

    return TEST_SUITE_END();
}