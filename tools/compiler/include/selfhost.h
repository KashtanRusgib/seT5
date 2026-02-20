/*
 * selfhost.h - Phase 5: Self-Hosting Compiler Interface
 *
 * The self-hosting compiler demonstrates that the Ternary-C toolchain
 * can compile a meaningful subset of its own source code (the tokenizer)
 * to ternary bytecode, and then execute said bytecode on the ternary VM
 * to correctly tokenize input.
 *
 * Self-hosting pipeline:
 *   1. A tokenizer is written in the seT5-C subset
 *   2. The bootstrap compiler compiles this tokenizer to bytecode
 *   3. The bytecode runs on the ternary VM
 *   4. The VM-resident tokenizer produces the same token stream
 *      as the native C tokenizer for the same input
 *
 * This completes the self-hosting circle:
 *   Compiler → compiles tokenizer → runs tokenizer → feeds back to compiler
 */

#ifndef SELFHOST_H
#define SELFHOST_H

#include "bootstrap.h"

#define SELFHOST_MAX_TOKENS 128

/* Token types produced by the self-hosted tokenizer */
typedef enum {
    SH_TOK_EOF = 0,
    SH_TOK_INT = 1,     /* integer literal */
    SH_TOK_IDENT = 2,   /* identifier */
    SH_TOK_PLUS = 3,    /* + */
    SH_TOK_MINUS = 4,   /* - */
    SH_TOK_STAR = 5,    /* * */
    SH_TOK_EQ = 6,      /* = */
    SH_TOK_SEMI = 7,    /* ; */
    SH_TOK_LPAREN = 8,  /* ( */
    SH_TOK_RPAREN = 9,  /* ) */
    SH_TOK_LBRACE = 10, /* { */
    SH_TOK_RBRACE = 11, /* } */
    SH_TOK_COMMA = 12,  /* , */
    SH_TOK_ERROR = 99
} SelfHostTokenType;

/* Result from a self-hosting test */
typedef struct {
    int tokens_produced;
    int tokens_matched;
    int compilation_ok;
    int execution_ok;
    int bytecode_len;
} SelfHostResult;

/*
 * selfhost_compile_tokenizer: Compile the self-hosted tokenizer
 * source to bytecode using the bootstrap compiler.
 * Returns bytecode length or -1 on error.
 */
int selfhost_compile_tokenizer(unsigned char *out_bytecode, int max_len);

/*
 * selfhost_run_tokenizer: Run the compiled tokenizer on the VM
 * with the given input source, producing tokens in memory.
 * Returns number of tokens produced, or -1 on error.
 */
int selfhost_run_tokenizer(const unsigned char *bytecode, int bc_len,
                            const char *input, int *out_tokens, int max_tokens);

/*
 * selfhost_verify: Full self-hosting verification.
 * Compiles tokenizer, runs it, and compares output with native tokenizer.
 * Returns 0 if all checks pass, nonzero on failure.
 */
int selfhost_verify(SelfHostResult *result);

/*
 * selfhost_roundtrip_test: Compile a seT5-C program with the bootstrap
 * compiler, run it on VM, and verify the result matches expected value.
 * Returns 0 on success.
 */
int selfhost_roundtrip_test(const char *source, int expected_result);

/*
 * selfhost_full_test: Run the complete self-hosting test battery.
 * Returns 0 on success, nonzero = number of failures.
 */
int selfhost_full_test(void);

#endif /* SELFHOST_H */
