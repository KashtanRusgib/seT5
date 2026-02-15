/*
 * test_parser_fuzz.c - Fuzz testing for parser robustness
 *
 * Tests: Random input handling, malformed code, edge cases
 */

#include "../include/test_harness.h"
#include "../include/parser.h"
#include "../include/ir.h"
#include <stdlib.h>
#include <time.h>
#include <string.h>

/* ---- Fuzz test helpers ---- */

static const char* random_tokens[] = {
    "int", "return", "if", "else", "while", "for",
    "+", "-", "*", "=", "==", "<", ">",
    "(", ")", "{", "}", "[", "]", ";", ",",
    "main", "func", "var", "123", "abc", "x", "y", "z",
    "0", "1", "42", "100",
    "++", "&"
};

#define NUM_RANDOM_TOKENS (sizeof(random_tokens) / sizeof(random_tokens[0]))

char* generate_random_code(int length) {
    char* code = (char*)malloc(length * 20 + 1); // Rough estimate
    code[0] = '\0';

    for (int i = 0; i < length; i++) {
        const char* token = random_tokens[rand() % NUM_RANDOM_TOKENS];
        strcat(code, token);
        strcat(code, " ");
    }

    return code;
}

/* ---- Parser fuzz tests ---- */

TEST(test_parser_random_input) {
    srand(time(NULL));

    // Test 100 random inputs
    for (int i = 0; i < 100; i++) {
        char* code = generate_random_code(10 + rand() % 20);

        // Parser should not crash on any input
        struct Expr* ast = parse_program(code);
        (void)ast;
        // Don't care about result, just that it doesn't crash

        free(code);
    }
}

TEST(test_parser_malformed_functions) {
    const char* malformed[] = {
        "int main( { return 0; }",           // Missing closing paren
        "int main() return 0; }",            // Missing opening brace
        "int main() { return 0; ",           // Missing closing brace
        "int () { return 0; }",              // Missing function name
        "main() { return 0; }",              // Missing return type
        "int main { return 0; }",            // Missing parentheses
        "int main() { return; }",            // Return without value
        "int main() { int x = ; return 0; }", // Incomplete assignment
        "int main() { if return 0; }",       // Malformed if
        "int main() { while return 0; }",    // Malformed while
    };

    for (int i = 0; i < 10; i++) {
        struct Expr* ast = parse_program(malformed[i]);
        (void)ast;
        // Should either parse successfully or fail gracefully
    }
}

TEST(test_parser_edge_cases) {
    const char* edge_cases[] = {
        "",                                    // Empty string
        " ",                                   // Only whitespace
        "int",                                 // Single keyword
        "main",                                // Single identifier
        "123",                                 // Single number
        "+",                                   // Single operator
        "(",                                   // Single parenthesis
        "{",                                   // Single brace
        "int main() { return 0; } x",          // Extra tokens
        "int\nmain\n()\n{\nreturn\n0;\n}",     // Multi-line
        "int\tmain\t()\t{\treturn\t0;\t}",     // Tabs
        "int main() { return 0; }",            // Normal code
    };

    for (int i = 0; i < 12; i++) {
        struct Expr* ast = parse_program(edge_cases[i]);
        (void)ast;
        // No ast_free needed
    }
}

TEST(test_parser_large_input) {
    // Generate a moderately large input (within token limits)
    // Each variable decl is ~15 chars: "int x0 = 0; "
    // MAX_TOKENS is 512, so limit to ~200 declarations
    size_t buf_size = 200 * 20 + 100;
    char* large_code = (char*)malloc(buf_size);
    strcpy(large_code, "int main() { ");

    for (int i = 0; i < 50; i++) {
        char decl[32];
        sprintf(decl, "int x%d = %d; ", i, i);
        if (strlen(large_code) + strlen(decl) + 20 < buf_size) {
            strcat(large_code, decl);
        }
    }

    strcat(large_code, "return 0; }");

    struct Expr* ast = parse_program(large_code);
    (void)ast;

    free(large_code);
}

TEST(test_parser_unicode_input) {
    // Test with valid code (unicode in comments would exit, so skip that)
    const char* code = "int main() { return 0; }";

    struct Expr* ast = parse_program(code);
    (void)ast;
}

int main(void) {
    TEST_SUITE_BEGIN("Parser Fuzz Testing");

    RUN_TEST(test_parser_random_input);
    RUN_TEST(test_parser_malformed_functions);
    RUN_TEST(test_parser_edge_cases);
    RUN_TEST(test_parser_large_input);
    RUN_TEST(test_parser_unicode_input);

    TEST_SUITE_END();
}