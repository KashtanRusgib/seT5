/* tools/compiler/tests/test_error_recovery.c - Error recovery mechanisms tests */
#include <stdio.h>
#include <setjmp.h>
#include "../include/test_harness.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"

jmp_buf recovery_buf;
int recovery_count = 0;

void error_recovery_handler(void) {
    recovery_count++;
    longjmp(recovery_buf, 1);
}

TEST(test_parser_error_recovery) {
    printf("Testing parser error recovery...\n");

    const char *error_cases[] = {
        "int x = ;",           // Missing expression
        "func( { return 1; }", // Missing closing paren
        "if ) { return 2; }",  // Wrong parenthesis
        "for int i = 0; i < 10; i++ { x++; }", // Missing paren
        "int arr[;",           // Incomplete array declaration
        "struct { int x; ",    // Missing closing brace
        "enum { A, B, ",       // Incomplete enum
        "switch x { case 1: break; }", // Missing paren
        "try throw 1; } catch (int e) { }", // Wrong braces
        "template T id(T x) { return x; }", // Missing typename
    };

    int num_cases = sizeof(error_cases) / sizeof(error_cases[0]);
    int recovered = 0;

    for (int i = 0; i < num_cases; i++) {
        recovery_count = 0;

        if (setjmp(recovery_buf) == 0) {
            // Set error handler
            set_error_handler(error_recovery_handler);

            tokenize(error_cases[i]);
            int result = parse();

            // Should have failed
            ASSERT_EQ(result, -1);
        } else {
            // Recovered from error
            recovered++;
        }

        // Restore default handler
        set_error_handler(NULL);
    }

    ASSERT_GT(recovered, 0);
    printf("  Recovered from %d/%d error cases\n", recovered, num_cases);
}

TEST(test_codegen_error_recovery) {
    printf("Testing codegen error recovery...\n");

    const char *invalid_code[] = {
        "int x = undefined_var;",  // Undefined variable
        "int arr[1000000000];",    // Too large array
        "void func() { goto invalid_label; }", // Invalid goto
        "int x = 1 / 0;",          // Division by zero in codegen
        "extern int x; x = 5;",    // Assigning to extern
        "const int x = 5; x = 10;", // Assigning to const
        "int x[5]; x[10] = 1;",    // Array bounds in codegen
    };

    int num_cases = sizeof(invalid_code) / sizeof(invalid_code[0]);
    int recovered = 0;

    for (int i = 0; i < num_cases; i++) {
        recovery_count = 0;

        if (setjmp(recovery_buf) == 0) {
            set_error_handler(error_recovery_handler);

            tokenize(invalid_code[i]);
            parse();
            codegen();

            // Should have failed during codegen
            ASSERT_EQ(last_error, ERR_CODEGEN_FAILED);
        } else {
            recovered++;
        }

        set_error_handler(NULL);
    }

    ASSERT_GT(recovered, 0);
    printf("  Recovered from %d/%d codegen errors\n", recovered, num_cases);
}

TEST(test_vm_error_recovery) {
    printf("Testing VM error recovery...\n");

    // Create bytecode that will cause runtime errors
    tokenize("int x = 1 / 0;"); // Division by zero
    parse();
    codegen();

    recovery_count = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        vm_run(bytecode, bc_idx);

        // Should have failed
        ASSERT_EQ(last_error, ERR_DIVISION_BY_ZERO);
    } else {
        // Recovered
        ASSERT_GT(recovery_count, 0);
    }

    set_error_handler(NULL);
}

TEST(test_memory_error_recovery) {
    printf("Testing memory error recovery...\n");

    recovery_count = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        // Try to allocate impossible amount
        void *ptr = malloc((size_t)-1);
        ASSERT_NULL(ptr);

        // This should trigger error recovery
        ASSERT_EQ(last_error, ERR_OUT_OF_MEMORY);
    } else {
        ASSERT_GT(recovery_count, 0);
    }

    set_error_handler(NULL);
}

TEST(test_nested_error_recovery) {
    printf("Testing nested error recovery...\n");

    int outer_recovered = 0;
    int inner_recovered = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        // Outer error
        tokenize("int x = ;");

        if (setjmp(recovery_buf) == 0) {
            // Inner error
            parse(); // This should fail
        } else {
            inner_recovered = 1;
        }

        // Continue and cause another error
        codegen(); // This might also fail

    } else {
        outer_recovered = 1;
    }

    set_error_handler(NULL);

    ASSERT_TRUE(outer_recovered || inner_recovered);
    printf("  Nested recovery: outer=%d, inner=%d\n", outer_recovered, inner_recovered);
}

TEST(test_error_context_preservation) {
    printf("Testing error context preservation...\n");

    const char *error_code = "int x = y + z;"; // Multiple undefined variables

    recovery_count = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        tokenize(error_code);
        parse();

        ASSERT_EQ(last_error, ERR_UNDEFINED_VARIABLE);
        // Should preserve information about which variable
        ASSERT_STR_EQ(error_var_name, "y"); // First undefined variable
    } else {
        ASSERT_GT(recovery_count, 0);
    }

    set_error_handler(NULL);
}

TEST(test_partial_recovery) {
    printf("Testing partial recovery...\n");

    // Code with multiple statements, some valid, some invalid
    const char *mixed_code =
        "int valid_var = 42;\n"
        "int invalid = ;\n"  // Error here
        "int another_valid = 123;\n";

    recovery_count = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        tokenize(mixed_code);
        parse();

        // Should have failed but recovered
        ASSERT_EQ(last_error, ERR_SYNTAX_ERROR);
    } else {
        // Check that we can still process valid parts
        ASSERT_TRUE(symbol_table_contains("valid_var"));
        ASSERT_FALSE(symbol_table_contains("invalid"));
        ASSERT_TRUE(symbol_table_contains("another_valid"));
    }

    set_error_handler(NULL);
}

TEST(test_error_reporting_accuracy) {
    printf("Testing error reporting accuracy...\n");

    const char *code_with_error = "int x = 5;\nint y = x +\nint z = 10;"; // Missing operand

    recovery_count = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        tokenize(code_with_error);
        parse();

        ASSERT_EQ(last_error, ERR_SYNTAX_ERROR);
        // Should report correct line number
        ASSERT_EQ(error_line, 2);
        ASSERT_EQ(error_column, 10); // Position of '+'
    } else {
        ASSERT_GT(recovery_count, 0);
    }

    set_error_handler(NULL);
}

TEST(test_resource_cleanup_on_error) {
    printf("Testing resource cleanup on error...\n");

    recovery_count = 0;
    int resources_allocated = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        // Allocate some resources
        resources_allocated = allocate_compiler_resources();

        // Cause an error
        tokenize("int x = @#$%;"); // Invalid tokens
        parse();

        ASSERT_EQ(last_error, ERR_LEXER_ERROR);
    } else {
        // Check that resources were cleaned up
        ASSERT_EQ(count_allocated_resources(), 0);
        printf("  Resources cleaned up: %d allocated before error\n", resources_allocated);
    }

    set_error_handler(NULL);
}

TEST(test_error_recovery_limits) {
    printf("Testing error recovery limits...\n");

    // Test that we don't recover infinitely
    const char *bad_code = "int x = ; int y = ; int z = ;";

    recovery_count = 0;
    int max_recoveries = 0;

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);

        tokenize(bad_code);
        parse();

        // Should have multiple errors but limited recoveries
        max_recoveries = 3; // Allow max 3 recoveries
    } else {
        recovery_count++;
        if (recovery_count >= max_recoveries) {
            // Stop recovering
            set_error_handler(NULL);
            longjmp(recovery_buf, 0); // Don't recover further
        }
    }

    set_error_handler(NULL);

    ASSERT_LE(recovery_count, max_recoveries);
    printf("  Limited recoveries: %d (max %d)\n", recovery_count, max_recoveries);
}

TEST(test_error_recovery_with_continuations) {
    printf("Testing error recovery with continuations...\n");

    const char *code_with_multiple_errors =
        "int a = 1;\n"
        "int b = ;\n"    // Error 1
        "int c = 2;\n"
        "int d = ;\n"    // Error 2
        "int e = 3;\n";

    recovery_count = 0;
    int continuations = 0;

    void continuation_handler(void) {
        continuations++;
        // Try to continue parsing after error
        if (continuations < 3) {
            longjmp(recovery_buf, 2); // Continue
        }
    }

    if (setjmp(recovery_buf) == 0) {
        set_error_handler(error_recovery_handler);
        set_continuation_handler(continuation_handler);

        tokenize(code_with_multiple_errors);
        parse();

    } else if (recovery_buf == 2) {
        // Continuation after error
        // Try to parse remaining code
        parse_remaining();
    }

    set_error_handler(NULL);
    set_continuation_handler(NULL);

    ASSERT_GT(continuations, 0);
    printf("  Error continuations: %d\n", continuations);
}

int main(void) {
    TEST_SUITE_BEGIN("Error Recovery Mechanisms");

    RUN_TEST(test_parser_error_recovery);
    RUN_TEST(test_codegen_error_recovery);
    RUN_TEST(test_vm_error_recovery);
    RUN_TEST(test_memory_error_recovery);
    RUN_TEST(test_nested_error_recovery);
    RUN_TEST(test_error_context_preservation);
    RUN_TEST(test_partial_recovery);
    RUN_TEST(test_error_reporting_accuracy);
    RUN_TEST(test_resource_cleanup_on_error);
    RUN_TEST(test_error_recovery_limits);
    RUN_TEST(test_error_recovery_with_continuations);

    TEST_SUITE_END();
}