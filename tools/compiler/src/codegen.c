#include <stdio.h>
#include "../include/codegen.h"
#include "../include/parser.h"
#include "../include/vm.h"
#include "../include/logger.h"

unsigned char bytecode[MAX_BYTECODE];
size_t bc_idx = 0;

static void emit(unsigned char op) {
    bytecode[bc_idx++] = op;
}

void codegen(void) {
    bc_idx = 0;
    LOG_DEBUG_MSG("Codegen", "TASK-006", "codegen entered");

    // Walk tokens and generate bytecode using operator precedence.
    // For the MVP, we handle expressions of the form:
    //   int (+ int)* with * binding tighter than +
    // Strategy: two-pass with deferred additions
    //
    // For now, emit RPN for the parsed token stream respecting * > + precedence.
    // We use a simple precedence-climbing approach over the flat token list.

    int i = 0;

    // Collect terms separated by '+', where each term is factors separated by '*'
    // term = factor (* factor)*
    // expr = term (+ term)*

    // We'll emit PUSH for each int, OP_MUL between factors, OP_ADD between terms.

    // Parse first factor of first term
    if (tokens[i].type != TOK_INT) {
        fprintf(stderr, "codegen: expected integer\n");
        return;
    }
    emit(OP_PUSH); emit((unsigned char)tokens[i].value);
    i++;

    // Continue within first term (handle * )
    while (tokens[i].type == TOK_MUL) {
        i++; // skip *
        if (tokens[i].type != TOK_INT) {
            fprintf(stderr, "codegen: expected integer after *\n");
            return;
        }
        emit(OP_PUSH); emit((unsigned char)tokens[i].value);
        i++;
        emit(OP_MUL);
    }

    // Handle remaining terms separated by + or -
    while (tokens[i].type == TOK_PLUS || tokens[i].type == TOK_MINUS) {
        int is_sub = (tokens[i].type == TOK_MINUS);
        i++; // skip + or -
        if (tokens[i].type != TOK_INT) {
            fprintf(stderr, "codegen: expected integer after %c\n", is_sub ? '-' : '+');
            return;
        }
        emit(OP_PUSH); emit((unsigned char)tokens[i].value);
        i++;

        // Handle * within this term
        while (tokens[i].type == TOK_MUL) {
            i++; // skip *
            if (tokens[i].type != TOK_INT) {
                fprintf(stderr, "codegen: expected integer after *\n");
                return;
            }
            emit(OP_PUSH); emit((unsigned char)tokens[i].value);
            i++;
            emit(OP_MUL);
        }

        emit(is_sub ? OP_SUB : OP_ADD);
    }

    emit(OP_HALT);
    LOG_DEBUG_MSG("Codegen", "TASK-006", "codegen complete");
}
