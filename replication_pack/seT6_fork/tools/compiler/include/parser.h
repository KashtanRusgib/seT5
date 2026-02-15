#ifndef PARSER_H
#define PARSER_H

/*
 * Token types for the ternary compiler lexer.
 * Phase 1: Arithmetic expressions
 * Phase 2: Keywords (for, while), identifiers, delimiters
 */
typedef enum {
    /* Literals */
    TOK_INT,        /* Integer literal (value in .value) */

    /* Operators */
    TOK_PLUS,       /* + */
    TOK_MINUS,      /* - */
    TOK_MUL,        /* * */
    TOK_PLUS_PLUS,  /* ++ */
    TOK_EQ,         /* = */
    TOK_LT,         /* < */
    TOK_AMP,        /* & (address-of) */

    /* Delimiters */
    TOK_LPAREN,     /* ( */
    TOK_RPAREN,     /* ) */
    TOK_LBRACE,     /* { */
    TOK_RBRACE,     /* } */
    TOK_SEMI,       /* ; */
    TOK_COMMA,      /* , */

    /* Keywords */
    TOK_FOR,        /* for */
    TOK_WHILE,      /* while */
    TOK_IF,         /* if */
    TOK_ELSE,       /* else */
    TOK_INT_KW,     /* int (keyword, distinct from TOK_INT literal) */
    TOK_RETURN,     /* return */

    /* Brackets */
    TOK_LBRACKET,   /* [ */
    TOK_RBRACKET,   /* ] */

    /* Multi-char operators */
    TOK_EQEQ,      /* == */
    TOK_GT,         /* > */

    /* Identifiers */
    TOK_IDENT,      /* identifier */

    /* Special */
    TOK_EOF
} TokenType;

typedef struct {
    TokenType type;
    int value;
} Token;

#define MAX_TOKENS 512

extern Token tokens[MAX_TOKENS];
extern int token_idx;

void tokenize(const char *source);
void parse(void);

#define MAX_TOKEN_NAME 64
extern char token_names[MAX_TOKENS][MAX_TOKEN_NAME];

/* Function/expression parser — returns AST (TASK-004) */
struct Expr;
struct Expr *parse_program(const char *source);

#endif
