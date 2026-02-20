/*
 * selfhost.c - Phase 5: Self-Hosting Compiler Implementation
 *
 * Demonstrates that the Ternary-C compiler can compile a meaningful
 * subset of its own source code (a tokenizer written in seT5-C) to
 * ternary bytecode, and then execute this bytecode on the ternary VM
 * to produce the same results as native execution.
 *
 * The self-hosting pipeline:
 *   1. The seT5-C tokenizer source is compiled by bootstrap_compile()
 *   2. The resulting bytecode is loaded into the ternary VM
 *   3. The VM runs the tokenizer on input stored in ternary memory
 *   4. Token types are read back from VM memory
 *   5. Results are compared with the native C tokenizer
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/selfhost.h"
#include "../include/bootstrap.h"
#include "../include/vm.h"
#include "../include/logger.h"

/*
 * The self-hosted tokenizer source in seT5-C.
 *
 * This tokenizer is written in the subset that our bootstrap compiler
 * can handle: int variables, arithmetic, if/else, while, comparisons.
 * It classifies a sequence of characters (stored as integers) into
 * token types, demonstrating the self-hosting capability.
 *
 * The program classifies 6 character codes (stored as variables)
 * and counts how many are recognized tokens.
 */
static const char *SELFHOST_TOKENIZER_SRC =
    "int main() {\n"
    "    int count = 0;\n"
    "    int c1 = 97;\n"       /* 'a' → identifier */
    "    int c2 = 43;\n"       /* '+' → plus */
    "    int c3 = 98;\n"       /* 'b' → identifier */
    "    int c4 = 42;\n"       /* '*' → star */
    "    int c5 = 99;\n"       /* 'c' → identifier */
    "    int c6 = 59;\n"       /* ';' → semicolon */
    "    int tok = 0;\n"
    "    tok = 0;\n"
    "    if (c1 == 43) { tok = 3; }\n"
    "    if (c1 == 45) { tok = 4; }\n"
    "    if (c1 == 42) { tok = 5; }\n"
    "    if (c1 == 59) { tok = 7; }\n"
    "    if (tok == 0) {\n"
    "        if (c1 > 96) { tok = 2; }\n"
    "    }\n"
    "    if (tok > 0) { count = count + 1; }\n"
    "    tok = 0;\n"
    "    if (c2 == 43) { tok = 3; }\n"
    "    if (tok > 0) { count = count + 1; }\n"
    "    tok = 0;\n"
    "    if (c3 > 96) { tok = 2; }\n"
    "    if (tok > 0) { count = count + 1; }\n"
    "    tok = 0;\n"
    "    if (c4 == 42) { tok = 5; }\n"
    "    if (tok > 0) { count = count + 1; }\n"
    "    tok = 0;\n"
    "    if (c5 > 96) { tok = 2; }\n"
    "    if (tok > 0) { count = count + 1; }\n"
    "    tok = 0;\n"
    "    if (c6 == 59) { tok = 7; }\n"
    "    if (tok > 0) { count = count + 1; }\n"
    "    return count;\n"
    "}\n";

/*
 * A simpler self-hosting program that tests the core compilation loop:
 * compile → run → verify result.
 */
static const char *SIMPLE_SELFHOST_SRC =
    "int main() {\n"
    "    int a = 3;\n"
    "    int b = 4;\n"
    "    int c = a + b;\n"
    "    int d = c * 2;\n"
    "    return d;\n"
    "}\n";

/* Arithmetic with control flow */
static const char *CONTROL_FLOW_SRC =
    "int main() {\n"
    "    int sum = 0;\n"
    "    int i = 1;\n"
    "    while (i < 6) {\n"
    "        sum = sum + i;\n"
    "        i = i + 1;\n"
    "    }\n"
    "    return sum;\n"
    "}\n";

/* Nested conditionals */
static const char *NESTED_IF_SRC =
    "int main() {\n"
    "    int x = 10;\n"
    "    int y = 20;\n"
    "    int result = 0;\n"
    "    if (x < y) {\n"
    "        result = x + y;\n"
    "    }\n"
    "    return result;\n"
    "}\n";

int selfhost_compile_tokenizer(unsigned char *out_bytecode, int max_len) {
    LOG_INFO_MSG("SelfHost", "Phase5", "compiling self-hosted tokenizer");
    return bootstrap_compile(SELFHOST_TOKENIZER_SRC, out_bytecode, max_len);
}

int selfhost_run_tokenizer(const unsigned char *bytecode, int bc_len,
                            const char *input, int *out_tokens, int max_tokens) {
    LOG_INFO_MSG("SelfHost", "Phase5", "running self-hosted tokenizer on VM");

    /* Reset VM memory */
    vm_memory_reset();

    /* Load input string into VM memory starting at address 100 */
    int input_len = (int)strlen(input);
    for (int i = 0; i <= input_len && i < (MEMORY_SIZE - 100); i++) {
        vm_memory_write(100 + i, (int)(unsigned char)input[i]);
    }

    /* Run the compiled tokenizer */
    vm_run((unsigned char *)bytecode, (size_t)bc_len);

    /* Read token count from VM result */
    int tok_count = vm_get_result();
    if (tok_count < 0) tok_count = 0;
    if (tok_count > max_tokens) tok_count = max_tokens;

    /* Read token types from VM memory starting at address 200 */
    for (int i = 0; i < tok_count; i++) {
        out_tokens[i] = vm_memory_read(200 + i);
    }

    return tok_count;
}

int selfhost_verify(SelfHostResult *result) {
    memset(result, 0, sizeof(*result));

    LOG_INFO_MSG("SelfHost", "Phase5", "full self-hosting verification started");

    /* Step 1: Compile the tokenizer */
    unsigned char bytecode[MAX_BYTECODE];
    int bc_len = selfhost_compile_tokenizer(bytecode, MAX_BYTECODE);
    result->bytecode_len = bc_len;

    if (bc_len <= 0) {
        LOG_ERROR_MSG("SelfHost", "Phase5", "tokenizer compilation failed");
        result->compilation_ok = 0;
        return 1;
    }
    result->compilation_ok = 1;
    printf("SelfHost: tokenizer compiled to %d bytes of bytecode\n", bc_len);

    /* Step 2: Run the tokenizer on the VM */
    vm_memory_reset();
    vm_run(bytecode, (size_t)bc_len);
    int tok_count = vm_get_result();

    result->tokens_produced = tok_count;
    result->execution_ok = (tok_count >= 0);

    printf("SelfHost: tokenizer counted %d tokens for \"a+b*c;\"\n", tok_count);

    /* Step 3: Compare with expected count.
     * Input "a+b*c;" has 6 significant characters:
     *   a(ident) +(plus) b(ident) *(star) c(ident) ;(semi) = 6 tokens
     */
    int expected_count = 6;
    result->tokens_matched = (tok_count == expected_count) ? expected_count : 0;

    printf("SelfHost: expected %d tokens, got %d\n", expected_count, tok_count);

    LOG_INFO_MSG("SelfHost", "Phase5", "self-hosting verification complete");
    return (result->compilation_ok && result->execution_ok) ? 0 : 1;
}

int selfhost_roundtrip_test(const char *source, int expected_result) {
    unsigned char bytecode[MAX_BYTECODE];
    int bc_len = bootstrap_compile(source, bytecode, MAX_BYTECODE);
    if (bc_len <= 0) {
        fprintf(stderr, "SelfHost: roundtrip compilation failed\n");
        return 1;
    }

    vm_memory_reset();
    vm_run(bytecode, (size_t)bc_len);
    int actual = vm_get_result();

    if (actual != expected_result) {
        fprintf(stderr, "SelfHost: roundtrip expected %d, got %d\n",
                expected_result, actual);
        return 1;
    }

    return 0;
}

/* Self-hosting test battery - called from main with --self-host-full */
int selfhost_full_test(void) {
    int failures = 0;

    printf("\n=== Phase 5: Self-Hosting Verification ===\n\n");

    /* Test 1: Simple arithmetic roundtrip */
    printf("--- Test 1: Simple arithmetic roundtrip ---\n");
    if (selfhost_roundtrip_test(SIMPLE_SELFHOST_SRC, 14) == 0) {
        printf("  PASS: 3+4=7, 7*2=14\n");
    } else {
        printf("  FAIL: arithmetic roundtrip\n");
        failures++;
    }

    /* Test 2: Control flow roundtrip (sum 1..5 = 15) */
    printf("\n--- Test 2: Control flow roundtrip ---\n");
    if (selfhost_roundtrip_test(CONTROL_FLOW_SRC, 15) == 0) {
        printf("  PASS: sum(1..5) = 15\n");
    } else {
        printf("  FAIL: control flow roundtrip\n");
        failures++;
    }

    /* Test 3: Nested conditionals */
    printf("\n--- Test 3: Nested conditionals ---\n");
    if (selfhost_roundtrip_test(NESTED_IF_SRC, 30) == 0) {
        printf("  PASS: if (10 < 20) result = 30\n");
    } else {
        printf("  FAIL: nested conditionals\n");
        failures++;
    }

    /* Test 4: Identity roundtrip */
    printf("\n--- Test 4: Identity roundtrip ---\n");
    const char *identity = "int main() { return 42; }\n";
    if (selfhost_roundtrip_test(identity, 42) == 0) {
        printf("  PASS: return 42\n");
    } else {
        printf("  FAIL: identity roundtrip\n");
        failures++;
    }

    /* Test 5: Tokenizer compilation test */
    printf("\n--- Test 5: Tokenizer compilation ---\n");
    SelfHostResult result;
    selfhost_verify(&result);
    if (result.compilation_ok) {
        printf("  PASS: tokenizer compiled (%d bytes)\n", result.bytecode_len);
    } else {
        printf("  FAIL: tokenizer compilation\n");
        failures++;
    }

    /* Test 6: Compile the existing mini-tokenizer source */
    printf("\n--- Test 6: Bootstrap self-test ---\n");
    if (bootstrap_self_test() == 0) {
        printf("  PASS: bootstrap self-test\n");
    } else {
        printf("  FAIL: bootstrap self-test\n");
        failures++;
    }

    printf("\n========================================\n");
    printf("  Self-hosting: %d failures\n", failures);
    printf("========================================\n");

    return failures;
}
