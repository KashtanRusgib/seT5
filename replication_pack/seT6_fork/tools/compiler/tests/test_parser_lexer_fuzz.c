/* tools/compiler/tests/test_parser_lexer_fuzz.c - Fuzz testing for parser and lexer */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "../include/test_harness.h"
#include "../include/parser.h"
#include "../include/parser.h"

#define FUZZ_ITERATIONS 1000
#define MAX_INPUT_SIZE 1024

TEST(test_lexer_fuzz_random_input) {
    printf("Testing lexer fuzz with random input...\n");

    srand(time(NULL));

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        // Generate random input
        char input[MAX_INPUT_SIZE];
        int len = rand() % (MAX_INPUT_SIZE - 1) + 1;

        for (int j = 0; j < len; j++) {
            input[j] = rand() % 256; // All possible byte values
        }
        input[len] = '\0';

        // Test lexer doesn't crash
        tokenize(input);

        // Verify basic invariants
        ASSERT_GE(tokens_count, 0);
        ASSERT_LE(tokens_count, MAX_TOKENS);

        // Check that we have an EOF token at the end (if tokens were produced)
        if (tokens_count > 0) {
            ASSERT_EQ(tokens[tokens_count - 1].type, TOK_EOF);
        }
    }
}

TEST(test_parser_fuzz_valid_syntax) {
    printf("Testing parser fuzz with valid syntax variations...\n");

    const char *valid_patterns[] = {
        "int x = 5;",
        "int func() { return 1; }",
        "if (1) { return 2; }",
        "for (int i = 0; i < 10; i++) { x++; }",
        "int arr[10];",
        "int *ptr = &x;",
        "struct S { int x; };",
        "typedef int myint;",
        "enum E { A, B, C };",
        "switch (x) { case 1: break; }",
        "try { throw 1; } catch (int e) { }",
        "template<typename T> T id(T x) { return x; }",
        "class C { public: int m; };",
        "namespace N { int x; }",
        "using namespace std;",
        "constexpr int N = 10;",
        "static_assert(1 == 1);",
        "decltype(x) y;",
        "alignas(16) int aligned;",
        "noexcept(true) void func();"
    };

    int num_patterns = sizeof(valid_patterns) / sizeof(valid_patterns[0]);

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        // Pick random valid pattern
        const char *pattern = valid_patterns[rand() % num_patterns];

        // Test parsing
        tokenize(pattern);
        int result = parse();

        // Should either succeed or fail gracefully (not crash)
        ASSERT_TRUE(result == 0 || result == -1);
    }
}

TEST(test_parser_fuzz_malformed_input) {
    printf("Testing parser fuzz with malformed input...\n");

    const char *malformed_patterns[] = {
        "int x = ;",
        "func( { return 1; }",
        "if ) { return 2; }",
        "for int i = 0; i < 10; i++ { x++; }",
        "int arr[;",
        "int *ptr = &;",
        "struct { int x; ",
        "typedef int",
        "enum { A, B, C ",
        "switch x { case 1: break; }",
        "try throw 1; } catch (int e) { }",
        "template T id(T x) { return x; }",
        "class { public: int m; };",
        "namespace { int x; }",
        "using std;",
        "constexpr N = 10;",
        "static_assert(1 == );",
        "decltype( y;",
        "alignas int aligned;",
        "noexcept void func();"
    };

    int num_patterns = sizeof(malformed_patterns) / sizeof(malformed_patterns[0]);

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        // Pick random malformed pattern
        const char *pattern = malformed_patterns[rand() % num_patterns];

        // Test parsing doesn't crash
        tokenize(pattern);
        int result = parse();

        // Should fail gracefully
        ASSERT_EQ(result, -1);
    }
}

TEST(test_lexer_fuzz_edge_cases) {
    printf("Testing lexer fuzz with edge cases...\n");

    const char *edge_cases[] = {
        "", // Empty string
        " ", // Single space
        "\t\n\r", // Whitespace only
        "/* comment */", // Comment only
        "// comment\n", // Line comment
        "\"string\"", // String literal
        "'c'", // Character literal
        "123456789", // Long number
        "0x123456789ABCDEF", // Hex number
        "123.456e-789", // Float
        "identifier_with_underscores_and_numbers_123",
        "!@#$%^&*()_+", // Symbols
        "int\x00float", // Null byte
        "trailing_spaces   \t\n  ",
        "/* nested /* comment */ */",
        "\"unterminated string",
        "'unterminated char",
        "0b10101010101010101010101010101010", // Binary
        "0o12345670", // Octal
        "999999999999999999999999999999999999999", // Very large number
        "\u00A9\u00AE\u2000\u3300", // Unicode
        "int\x01\x02\x03float", // Control characters
        "a/*comment*/b",
        "x//comment\ny",
        "\"string with \\\" escape\"",
        "'\\n\\t\\''"
    };

    int num_cases = sizeof(edge_cases) / sizeof(edge_cases[0]);

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        // Pick random edge case
        const char *input = edge_cases[rand() % num_cases];

        // Test lexer doesn't crash
        tokenize(input);

        // Basic sanity checks
        ASSERT_GE(tokens_count, 0);
        ASSERT_LE(tokens_count, MAX_TOKENS);
    }
}

TEST(test_parser_fuzz_nested_structures) {
    printf("Testing parser fuzz with nested structures...\n");

    for (int i = 0; i < FUZZ_ITERATIONS / 10; i++) { // Fewer iterations for complex cases
        char buffer[4096];
        int depth = rand() % 5 + 1; // Nesting depth 1-5

        // Generate nested if statements
        strcpy(buffer, "int x = 1;");
        for (int d = 0; d < depth; d++) {
            strcat(buffer, "if (x) {");
        }
        strcat(buffer, "x = 42;");
        for (int d = 0; d < depth; d++) {
            strcat(buffer, "}");
        }

        // Test parsing
        tokenize(buffer);
        int result = parse();

        // Should parse successfully
        ASSERT_EQ(result, 0);
    }
}

TEST(test_lexer_fuzz_large_input) {
    printf("Testing lexer fuzz with large input...\n");

    // Generate large input with repeated patterns
    char *large_input = malloc(100000);
    ASSERT_NOT_NULL(large_input);

    strcpy(large_input, "");
    for (int i = 0; i < 1000; i++) {
        strcat(large_input, "int x");
        char num[16];
        sprintf(num, "%d", i);
        strcat(large_input, num);
        strcat(large_input, " = ");
        strcat(large_input, num);
        strcat(large_input, "; ");
    }

    // Test lexer handles large input
    tokenize(large_input);

    ASSERT_GT(tokens_count, 0);
    ASSERT_LE(tokens_count, MAX_TOKENS);

    free(large_input);
}

TEST(test_parser_fuzz_arithmetic_expressions) {
    printf("Testing parser fuzz with arithmetic expressions...\n");

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        char expr[256];
        int len = rand() % 10 + 1; // Expression length

        strcpy(expr, "");
        for (int j = 0; j < len; j++) {
            if (j > 0) {
                const char *ops[] = {"+", "-", "*", "/", "%", "&", "|", "^", "<<", ">>"};
                strcat(expr, ops[rand() % 10]);
            }

            if (rand() % 2) {
                char num[16];
                sprintf(num, "%d", rand() % 100);
                strcat(expr, num);
            } else {
                const char *vars[] = {"x", "y", "z", "a", "b", "c"};
                strcat(expr, vars[rand() % 6]);
            }

            if (rand() % 3 == 0) { // Add parentheses sometimes
                strcat(expr, "(");
                char num[16];
                sprintf(num, "%d", rand() % 10);
                strcat(expr, num);
                strcat(expr, ")");
            }
        }

        // Test parsing expression
        tokenize(expr);
        int result = parse_expression();

        // Should either succeed or fail gracefully
        ASSERT_TRUE(result == 0 || result == -1);
    }
}

TEST(test_lexer_fuzz_unicode_identifiers) {
    printf("Testing lexer fuzz with unicode identifiers...\n");

    // Test various unicode identifier patterns
    const char *unicode_ids[] = {
        "变量", // Chinese
        "переменная", // Russian
        "variable", // ASCII
        "变量_123", // Mixed
        "αβγ", // Greek
        "δέλτα", // Greek word
        "функция", // Russian
        "函数", // Chinese
        "método", // Spanish with accent
        " naïve", // With diaeresis
        "Zürich", // German umlaut
        "naïve_café", // Multiple accents
        "Προγραμματισμός", // Greek
        "프로그래밍", // Korean
        "プログラミング", // Japanese
        "برمجة", // Arabic
        "תכנות", // Hebrew
    };

    int num_ids = sizeof(unicode_ids) / sizeof(unicode_ids[0]);

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        char buffer[256];
        const char *id = unicode_ids[rand() % num_ids];

        // Create declaration with unicode identifier
        sprintf(buffer, "int %s = 42;", id);

        // Test lexer handles unicode
        tokenize(buffer);

        ASSERT_GT(tokens_count, 0);
        // Should have int, identifier, =, number, ;, EOF
        ASSERT_GE(tokens_count, 6);
    }
}

TEST(test_parser_fuzz_error_recovery) {
    printf("Testing parser fuzz with error recovery...\n");

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        char buffer[1024];

        // Generate code with random syntax errors
        int num_stmts = rand() % 5 + 1;
        strcpy(buffer, "");

        for (int s = 0; s < num_stmts; s++) {
            if (rand() % 2) {
                // Valid statement
                strcat(buffer, "int x = 5;");
            } else {
                // Invalid statement
                const char *invalid[] = {
                    "int x = ;",
                    "x = 5",
                    "if ( { }",
                    "for (int i = 0; i < 10 i++) { }",
                    "func( { return 1; }",
                    "struct { int x; ",
                    "enum { A, B ",
                };
                strcat(buffer, invalid[rand() % 7]);
            }
        }

        // Test parser error recovery
        tokenize(buffer);
        int result = parse();

        // Should handle errors gracefully
        ASSERT_TRUE(result == 0 || result == -1);

        // Even with errors, should have made progress
        ASSERT_GE(tokens_count, 0);
    }
}

TEST(test_lexer_fuzz_numeric_literals) {
    printf("Testing lexer fuzz with numeric literals...\n");

    const char *numbers[] = {
        "0", "1", "-1", "123", "-456",
        "0x0", "0x1", "0xFF", "0x123456789ABCDEF",
        "0b0", "0b1", "0b101010", "0b11111111",
        "0o0", "0o7", "0o777", "0o1234567",
        "0.0", "1.5", "-2.25", "123.456",
        "1e10", "1.5e-5", "-2.3E+7",
        "0x1.8p3", "0b1.01p2",
        "999999999999999999999999999999999999999",
        "0.000000000000000000000000000000000001",
        "1e1000", "1e-1000"
    };

    int num_numbers = sizeof(numbers) / sizeof(numbers[0]);

    for (int i = 0; i < FUZZ_ITERATIONS; i++) {
        const char *num = numbers[rand() % num_numbers];

        // Test lexing number
        tokenize(num);

        // Should produce at least one token
        ASSERT_GT(tokens_count, 0);

        // First token should be a number
        ASSERT_TRUE(tokens[0].type == TOK_INT || tokens[0].type == TOK_FLOAT);
    }
}

int main(void) {
    TEST_SUITE_BEGIN("Parser/Lexer Fuzz Testing");

    RUN_TEST(test_lexer_fuzz_random_input);
    RUN_TEST(test_parser_fuzz_valid_syntax);
    RUN_TEST(test_parser_fuzz_malformed_input);
    RUN_TEST(test_lexer_fuzz_edge_cases);
    RUN_TEST(test_parser_fuzz_nested_structures);
    RUN_TEST(test_lexer_fuzz_large_input);
    RUN_TEST(test_parser_fuzz_arithmetic_expressions);
    RUN_TEST(test_lexer_fuzz_unicode_identifiers);
    RUN_TEST(test_parser_fuzz_error_recovery);
    RUN_TEST(test_lexer_fuzz_numeric_literals);

    TEST_SUITE_END();
}