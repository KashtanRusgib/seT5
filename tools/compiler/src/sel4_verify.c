/*
 * sel4_verify.c - seL4 Ternary Compilation and Verification (TASK-019)
 *
 * Compiles seL4 kernel stubs through the full ternary pipeline
 * and provides verification hooks for Isabelle proofs.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/sel4_verify.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"
#include "../include/logger.h"

int sel4_compile_full(const char *source, unsigned char *out, int max_len) {
    LOG_INFO_MSG("seL4", "TASK-019", "sel4_compile_full entered");

    /* Use the existing pipeline: tokenize -> parse -> codegen */
    tokenize(source);
    parse();
    codegen();

    int len = (int)bc_idx;
    if (len > max_len) len = max_len;
    for (int i = 0; i < len; i++) {
        out[i] = bytecode[i];
    }

    LOG_INFO_MSG("seL4", "TASK-019", "sel4_compile_full complete");
    return len;
}
