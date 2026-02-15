/* Standalone VM test - demonstrates bytecode execution */
#include <stdio.h>
#include "../include/vm.h"

int main(void) {
    // Test bytecode: PUSH 1, PUSH 2, PUSH 3, MUL, ADD, HALT
    // Expected: 1 + (2 * 3) = 7
    unsigned char code[] = {
        OP_PUSH, 1,
        OP_PUSH, 2,
        OP_PUSH, 3,
        OP_MUL,
        OP_ADD,
        OP_HALT
    };
    vm_run(code, sizeof(code));
    return 0;
}
