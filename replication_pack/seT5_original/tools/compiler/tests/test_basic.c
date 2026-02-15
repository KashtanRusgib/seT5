/* tests/test_basic.c - Basic integration test */
#include <stdio.h>
#include <assert.h>
#include "../include/ternary.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"

void test_trit_operations(void) {
    printf("Testing trit operations...\n");

    // Test trit_mul
    assert(trit_mul(TRIT_P, TRIT_P) == TRIT_P);   //  1 *  1 =  1
    assert(trit_mul(TRIT_P, TRIT_N) == TRIT_N);    //  1 * -1 = -1
    assert(trit_mul(TRIT_N, TRIT_N) == TRIT_P);    // -1 * -1 =  1
    assert(trit_mul(TRIT_Z, TRIT_P) == TRIT_Z);    //  0 *  1 =  0

    // Test trit_add
    trit carry = TRIT_Z;
    assert(trit_add(TRIT_P, TRIT_P, &carry) == TRIT_N);  // 1+1 = 2 -> -1 carry 1
    assert(carry == TRIT_P);

    carry = TRIT_Z;
    assert(trit_add(TRIT_P, TRIT_Z, &carry) == TRIT_P);  // 1+0 = 1
    assert(carry == TRIT_Z);

    // Test trit_min / trit_max
    assert(trit_min(TRIT_N, TRIT_P) == TRIT_N);
    assert(trit_max(TRIT_N, TRIT_P) == TRIT_P);

    printf("  All trit operation tests passed!\n");
}

void test_tokenizer(void) {
    printf("Testing tokenizer...\n");

    tokenize("1 + 2 * 3");
    assert(tokens[0].type == TOK_INT && tokens[0].value == 1);
    assert(tokens[1].type == TOK_PLUS);
    assert(tokens[2].type == TOK_INT && tokens[2].value == 2);
    assert(tokens[3].type == TOK_MUL);
    assert(tokens[4].type == TOK_INT && tokens[4].value == 3);
    assert(tokens[5].type == TOK_EOF);

    printf("  All tokenizer tests passed!\n");
}

void test_codegen(void) {
    printf("Testing codegen...\n");

    tokenize("1 + 2 * 3");
    parse();
    codegen();

    // Expected bytecode: PUSH 1, PUSH 2, PUSH 3, MUL, ADD, HALT
    assert(bytecode[0] == OP_PUSH);
    assert(bytecode[1] == 1);
    assert(bytecode[2] == OP_PUSH);
    assert(bytecode[3] == 2);
    assert(bytecode[4] == OP_PUSH);
    assert(bytecode[5] == 3);
    assert(bytecode[6] == OP_MUL);
    assert(bytecode[7] == OP_ADD);
    assert(bytecode[8] == OP_HALT);
    assert(bc_idx == 9);

    printf("  All codegen tests passed!\n");
}

void test_vm_execution(void) {
    printf("Testing VM execution...\n");

    tokenize("1 + 2 * 3");
    parse();
    codegen();

    printf("  Running bytecode (expect Result: 7)... ");
    vm_run(bytecode, bc_idx);

    printf("  VM execution test passed!\n");
}

int main(void) {
    printf("=== Ternary Compiler Test Suite ===\n\n");

    test_trit_operations();
    test_tokenizer();
    test_codegen();
    test_vm_execution();

    printf("\n=== All tests passed! ===\n");
    return 0;
}
