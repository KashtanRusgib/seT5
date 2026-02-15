/*
 * test_lexer.c - Unit tests for the tokenizer/lexer
 *
 * Tests: tokenize() from parser.c
 * Coverage: valid expressions, whitespace, multi-digit ints,
 *           edge cases, invalid characters
 */

#include "../include/test_harness.h"
#include "../include/parser.h"

/* ---- Basic tokenization ---- */

TEST(test_single_integer) {
    tokenize("42");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 42);
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

TEST(test_simple_addition) {
    tokenize("1 + 2");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 1);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 2);
    ASSERT_EQ(tokens[3].type, TOK_EOF);
}

TEST(test_simple_multiplication) {
    tokenize("3 * 4");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 3);
    ASSERT_EQ(tokens[1].type, TOK_MUL);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 4);
    ASSERT_EQ(tokens[3].type, TOK_EOF);
}

TEST(test_mixed_operators) {
    tokenize("1 + 2 * 3");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 1);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 2);
    ASSERT_EQ(tokens[3].type, TOK_MUL);
    ASSERT_EQ(tokens[4].type, TOK_INT);
    ASSERT_EQ(tokens[4].value, 3);
    ASSERT_EQ(tokens[5].type, TOK_EOF);
}

/* ---- Whitespace handling ---- */

TEST(test_no_spaces) {
    tokenize("1+2");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 1);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 2);
    ASSERT_EQ(tokens[3].type, TOK_EOF);
}

TEST(test_extra_spaces) {
    tokenize("  1   +   2  ");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 1);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 2);
    ASSERT_EQ(tokens[3].type, TOK_EOF);
}

TEST(test_tabs_and_newlines) {
    tokenize("\t1\n+\t2\n");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 1);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 2);
    ASSERT_EQ(tokens[3].type, TOK_EOF);
}

/* ---- Multi-digit integers ---- */

TEST(test_multi_digit) {
    tokenize("123 + 456");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 123);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 456);
    ASSERT_EQ(tokens[3].type, TOK_EOF);
}

TEST(test_zero) {
    tokenize("0");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 0);
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

/* ---- Complex expressions ---- */

TEST(test_long_expression) {
    tokenize("1 + 2 + 3 + 4");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 1);
    ASSERT_EQ(tokens[1].type, TOK_PLUS);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 2);
    ASSERT_EQ(tokens[3].type, TOK_PLUS);
    ASSERT_EQ(tokens[4].type, TOK_INT);
    ASSERT_EQ(tokens[4].value, 3);
    ASSERT_EQ(tokens[5].type, TOK_PLUS);
    ASSERT_EQ(tokens[6].type, TOK_INT);
    ASSERT_EQ(tokens[6].value, 4);
    ASSERT_EQ(tokens[7].type, TOK_EOF);
}

TEST(test_chained_multiplication) {
    tokenize("2 * 3 * 4");
    ASSERT_EQ(tokens[0].type, TOK_INT);
    ASSERT_EQ(tokens[0].value, 2);
    ASSERT_EQ(tokens[1].type, TOK_MUL);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 3);
    ASSERT_EQ(tokens[3].type, TOK_MUL);
    ASSERT_EQ(tokens[4].type, TOK_INT);
    ASSERT_EQ(tokens[4].value, 4);
    ASSERT_EQ(tokens[5].type, TOK_EOF);
}

/* ---- Edge case: empty input ---- */

TEST(test_empty_string) {
    tokenize("");
    ASSERT_EQ(tokens[0].type, TOK_EOF);
}

TEST(test_whitespace_only) {
    tokenize("   \t\n  ");
    ASSERT_EQ(tokens[0].type, TOK_EOF);
}

/* ---- Keyword tokenization (TASK-001) ---- */

TEST(test_for_keyword) {
    tokenize("for");
    ASSERT_EQ(tokens[0].type, TOK_FOR);
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

TEST(test_while_keyword) {
    tokenize("while");
    ASSERT_EQ(tokens[0].type, TOK_WHILE);
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

TEST(test_for_loop_structure) {
    tokenize("for (int i=0; i<10; i++) { }");
    ASSERT_EQ(tokens[0].type, TOK_FOR);
    ASSERT_EQ(tokens[1].type, TOK_LPAREN);
    ASSERT_EQ(tokens[2].type, TOK_INT_KW);
    ASSERT_EQ(tokens[3].type, TOK_IDENT);
    ASSERT_EQ(tokens[4].type, TOK_EQ);
    ASSERT_EQ(tokens[5].type, TOK_INT);
    ASSERT_EQ(tokens[5].value, 0);
    ASSERT_EQ(tokens[6].type, TOK_SEMI);
    ASSERT_EQ(tokens[7].type, TOK_IDENT);
    ASSERT_EQ(tokens[8].type, TOK_LT);
    ASSERT_EQ(tokens[9].type, TOK_INT);
    ASSERT_EQ(tokens[9].value, 10);
    ASSERT_EQ(tokens[10].type, TOK_SEMI);
    ASSERT_EQ(tokens[11].type, TOK_IDENT);
    ASSERT_EQ(tokens[12].type, TOK_PLUS_PLUS);
    ASSERT_EQ(tokens[13].type, TOK_RPAREN);
    ASSERT_EQ(tokens[14].type, TOK_LBRACE);
    ASSERT_EQ(tokens[15].type, TOK_RBRACE);
    ASSERT_EQ(tokens[16].type, TOK_EOF);
}

TEST(test_invalid_loop_keyword) {
    tokenize("forr");
    ASSERT_EQ(tokens[0].type, TOK_IDENT);
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

/* ---- Return keyword and comma (TASK-004 support) ---- */

TEST(test_return_keyword) {
    tokenize("return");
    ASSERT_EQ(tokens[0].type, TOK_RETURN);
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

TEST(test_comma_token) {
    tokenize("foo(1, 2)");
    ASSERT_EQ(tokens[0].type, TOK_IDENT);
    ASSERT_EQ(tokens[1].type, TOK_LPAREN);
    ASSERT_EQ(tokens[2].type, TOK_INT);
    ASSERT_EQ(tokens[2].value, 1);
    ASSERT_EQ(tokens[3].type, TOK_COMMA);
    ASSERT_EQ(tokens[4].type, TOK_INT);
    ASSERT_EQ(tokens[4].value, 2);
    ASSERT_EQ(tokens[5].type, TOK_RPAREN);
    ASSERT_EQ(tokens[6].type, TOK_EOF);
}

TEST(test_ident_name_storage) {
    tokenize("myVar");
    ASSERT_EQ(tokens[0].type, TOK_IDENT);
    ASSERT_STR_EQ(token_names[0], "myVar");
    ASSERT_EQ(tokens[1].type, TOK_EOF);
}

int main(void) {
    TEST_SUITE_BEGIN("Lexer/Tokenizer");

    RUN_TEST(test_single_integer);
    RUN_TEST(test_simple_addition);
    RUN_TEST(test_simple_multiplication);
    RUN_TEST(test_mixed_operators);
    RUN_TEST(test_no_spaces);
    RUN_TEST(test_extra_spaces);
    RUN_TEST(test_tabs_and_newlines);
    RUN_TEST(test_multi_digit);
    RUN_TEST(test_zero);
    RUN_TEST(test_long_expression);
    RUN_TEST(test_chained_multiplication);
    RUN_TEST(test_empty_string);
    RUN_TEST(test_whitespace_only);
    RUN_TEST(test_for_keyword);
    RUN_TEST(test_while_keyword);
    RUN_TEST(test_for_loop_structure);
    RUN_TEST(test_invalid_loop_keyword);
    RUN_TEST(test_return_keyword);
    RUN_TEST(test_comma_token);
    RUN_TEST(test_ident_name_storage);

    TEST_SUITE_END();
}
