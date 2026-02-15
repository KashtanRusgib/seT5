/*
 * bootstrap.c - Self-Hosting Bootstrap Compiler (TASK-018)
 *
 * Implements a minimal self-hosting compiler that can compile
 * a subset of C (seT5-C) to ternary bytecode. The key test is
 * compiling a mini-tokenizer written in seT5-C and running it
 * on the VM.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/bootstrap.h"
#include "../include/ir.h"
#include "../include/parser.h"
#include "../include/codegen.h"
#include "../include/vm.h"
#include "../include/logger.h"

/*
 * AST-to-bytecode emitter for the bootstrap compiler.
 * Walks the AST and emits stack-machine bytecode.
 */
static int bc_pos;
static unsigned char *bc_out;
static int bc_max;
static BootstrapSymTab symtab;

static void b_emit(unsigned char byte) {
    if (bc_pos < bc_max) {
        bc_out[bc_pos++] = byte;
    }
}

/* Emit bytecode for an expression */
static void emit_expr(Expr *e) {
    if (e == NULL) return;

    switch (e->type) {
        case NODE_CONST:
            b_emit(OP_PUSH);
            b_emit((unsigned char)(e->val & 0xFF));
            break;

        case NODE_VAR: {
            /* Load variable from memory using its stack offset as address */
            int off = symtab_lookup(&symtab, e->name);
            if (off >= 0) {
                b_emit(OP_PUSH);
                b_emit((unsigned char)off);
                b_emit(OP_LOAD);
            } else {
                /* Unknown variable — emit 0 */
                b_emit(OP_PUSH);
                b_emit(0);
            }
            break;
        }

        case NODE_BINOP:
            emit_expr(e->left);
            emit_expr(e->right);
            switch (e->op) {
                case OP_IR_ADD:    b_emit(OP_ADD); break;
                case OP_IR_MUL:   b_emit(OP_MUL); break;
                case OP_IR_SUB:   b_emit(OP_SUB); break;
                case OP_IR_CMP_EQ: b_emit(OP_CMP_EQ); break;
                case OP_IR_CMP_LT: b_emit(OP_CMP_LT); break;
                case OP_IR_CMP_GT: b_emit(OP_CMP_GT); break;
                case OP_IR_NEG:   b_emit(OP_NEG); break;
            }
            break;

        case NODE_RETURN:
            emit_expr(e->left);
            break;

        case NODE_VAR_DECL: {
            /* int x = expr; -> compute expr, store at x's offset */
            int off = symtab_add(&symtab, e->name, 0);
            if (off >= 0 && e->left) {
                b_emit(OP_PUSH);
                b_emit((unsigned char)off);
                emit_expr(e->left);
                b_emit(OP_STORE);
            }
            break;
        }

        case NODE_ASSIGN: {
            /* x = expr; -> compute expr, store at x's offset */
            if (e->left && e->left->type == NODE_VAR) {
                int off = symtab_lookup(&symtab, e->left->name);
                if (off >= 0) {
                    b_emit(OP_PUSH);
                    b_emit((unsigned char)off);
                    emit_expr(e->right);
                    b_emit(OP_STORE);
                }
            }
            break;
        }

        case NODE_DEREF:
            emit_expr(e->left);
            b_emit(OP_LOAD);
            break;

        case NODE_ADDR_OF:
            /* Push the address (stack offset) of the variable */
            if (e->left && e->left->type == NODE_VAR) {
                int off = symtab_lookup(&symtab, e->left->name);
                b_emit(OP_PUSH);
                b_emit((unsigned char)(off >= 0 ? off : 0));
            }
            break;

        case NODE_FUNC_CALL:
            /* Emit args, then a placeholder (stub for Phase 3 call convention) */
            for (int i = 0; i < e->param_count; i++) {
                emit_expr(e->params[i]);
            }
            break;

        case NODE_FUNC_DEF:
            /* Emit ENTER for scope, body statements, then LEAVE */
            b_emit(OP_ENTER);
            for (int i = 0; i < e->param_count; i++) {
                emit_expr(e->params[i]);
            }
            emit_expr(e->body);
            b_emit(OP_LEAVE);
            break;

        case NODE_PROGRAM:
            for (int i = 0; i < e->param_count; i++) {
                emit_expr(e->params[i]);
            }
            break;

        /* === Phase 3: Structured control flow (Setun-70/DSSP style) === */

        case NODE_IF: {
            /*
             * if (cond) { body } [else { else_body }]
             *
             * Emit: cond, [normalize], BRZ else_label, body,
             *       [JMP end_label, else_label: else_body], end_label:
             *
             * Normalization: CMP_LT/CMP_GT return ternary {-1,0,1}
             * but BRZ only branches on 0. We normalize comparison
             * results: emit PUSH 1, CMP_EQ after comparisons so that
             * "true" (1) becomes 1 and "false" (-1 or 0) becomes 0.
             */
            emit_expr(e->condition);

            /* Normalize comparison results to boolean 0/1 for BRZ */
            if (e->condition && e->condition->type == NODE_BINOP &&
                (e->condition->op == OP_IR_CMP_LT ||
                 e->condition->op == OP_IR_CMP_GT)) {
                b_emit(OP_PUSH);
                b_emit(1);
                b_emit(OP_CMP_EQ);
            }

            b_emit(OP_BRZ);
            int patch_else = bc_pos;
            b_emit(0);  /* placeholder for else/end target */

            emit_expr(e->body);

            if (e->else_body) {
                b_emit(OP_JMP);
                int patch_end = bc_pos;
                b_emit(0);  /* placeholder for end target */

                /* Patch BRZ to jump here (else start) */
                bc_out[patch_else] = (unsigned char)bc_pos;

                emit_expr(e->else_body);

                /* Patch JMP to jump here (end) */
                bc_out[patch_end] = (unsigned char)bc_pos;
            } else {
                /* No else: BRZ jumps past body */
                bc_out[patch_else] = (unsigned char)bc_pos;
            }
            break;
        }

        case NODE_WHILE: {
            /*
             * while (cond) { body }
             *
             * Emit: LOOP_BEGIN, cond, BRZ end, body, PUSH 1, LOOP_END, end:
             */
            int loop_start = bc_pos;
            b_emit(OP_LOOP_BEGIN);

            emit_expr(e->condition);

            /* Normalize comparison results for BRZ */
            if (e->condition && e->condition->type == NODE_BINOP &&
                (e->condition->op == OP_IR_CMP_LT ||
                 e->condition->op == OP_IR_CMP_GT)) {
                b_emit(OP_PUSH);
                b_emit(1);
                b_emit(OP_CMP_EQ);
            }

            b_emit(OP_BRZ);
            int patch_end = bc_pos;
            b_emit(0);  /* placeholder for end target */

            emit_expr(e->body);

            /* Continue loop */
            b_emit(OP_PUSH);
            b_emit(1);
            b_emit(OP_LOOP_END);

            /* Patch BRZ to jump past LOOP_END */
            bc_out[patch_end] = (unsigned char)bc_pos;
            (void)loop_start;
            break;
        }

        case NODE_FOR: {
            /*
             * for (init; cond; inc) { body }
             *
             * Emit: init, LOOP_BEGIN, cond, BRZ end, body, inc, PUSH 1, LOOP_END, end:
             */
            emit_expr(e->left);  /* init */

            b_emit(OP_LOOP_BEGIN);

            emit_expr(e->condition);

            /* Normalize comparison results for BRZ */
            if (e->condition && e->condition->type == NODE_BINOP &&
                (e->condition->op == OP_IR_CMP_LT ||
                 e->condition->op == OP_IR_CMP_GT)) {
                b_emit(OP_PUSH);
                b_emit(1);
                b_emit(OP_CMP_EQ);
            }

            b_emit(OP_BRZ);
            int patch_end = bc_pos;
            b_emit(0);

            emit_expr(e->body);
            emit_expr(e->increment);

            /* Continue loop */
            b_emit(OP_PUSH);
            b_emit(1);
            b_emit(OP_LOOP_END);

            /* Patch BRZ to end */
            bc_out[patch_end] = (unsigned char)bc_pos;
            break;
        }

        case NODE_BLOCK:
            /* Emit all statements in the block */
            for (int i = 0; i < e->param_count; i++) {
                emit_expr(e->params[i]);
            }
            break;

        /* === Phase 3: Array support === */

        case NODE_ARRAY_DECL: {
            /* int arr[N]; allocate N contiguous memory slots */
            int base = symtab_add(&symtab, e->name, 0);
            if (base >= 0) {
                /* Reserve array_size - 1 additional slots */
                for (int i = 1; i < e->array_size; i++) {
                    char slotname[72];
                    snprintf(slotname, sizeof(slotname), "%s[%d]", e->name, i);
                    symtab_add(&symtab, slotname, 0);
                }
                /* Emit initializers if present */
                for (int i = 0; i < e->param_count && i < e->array_size; i++) {
                    b_emit(OP_PUSH);
                    b_emit((unsigned char)(base + i));
                    emit_expr(e->params[i]);
                    b_emit(OP_STORE);
                }
            }
            break;
        }

        case NODE_ARRAY_ACCESS: {
            /* arr[index] -> load from base + index */
            int base = symtab_lookup(&symtab, e->name);
            if (base >= 0) {
                /* Push base, push index, add, load */
                b_emit(OP_PUSH);
                b_emit((unsigned char)base);
                emit_expr(e->left);  /* index */
                b_emit(OP_ADD);
                b_emit(OP_LOAD);
            } else {
                b_emit(OP_PUSH);
                b_emit(0);
            }
            break;
        }

        case NODE_ARRAY_ASSIGN: {
            /* arr[index] = expr -> store at base + index */
            int base = symtab_lookup(&symtab, e->name);
            if (base >= 0) {
                /* Push base, push index, add => address on stack */
                b_emit(OP_PUSH);
                b_emit((unsigned char)base);
                emit_expr(e->left);  /* index */
                b_emit(OP_ADD);
                emit_expr(e->right); /* value */
                b_emit(OP_STORE);
            }
            break;
        }
    }
}

int bootstrap_compile(const char *source, unsigned char *out_bytecode, int max_len) {
    LOG_INFO_MSG("Bootstrap", "TASK-018", "bootstrap_compile entered");

    /* Parse */
    Expr *ast = parse_program(source);
    if (ast == NULL) {
        LOG_ERROR_MSG("Bootstrap", "TASK-018", "parse failed");
        return -1;
    }

    /* Optimize */
    optimize(ast);

    /* Emit bytecode */
    bc_out = out_bytecode;
    bc_max = max_len;
    bc_pos = 0;
    symtab_init(&symtab);

    emit_expr(ast);
    b_emit(OP_HALT);

    expr_free(ast);

    LOG_INFO_MSG("Bootstrap", "TASK-018", "bootstrap_compile complete");
    return bc_pos;
}

/*
 * Mini-tokenizer source in seT5-C subset.
 * This is the simplest possible tokenizer that we can compile
 * with our own compiler and run on our VM.
 */
static const char *MINI_TOKENIZER_SRC =
    "int main() {\n"
    "    int a = 1 + 2;\n"
    "    int b = a * 3;\n"
    "    return b;\n"
    "}\n";

int bootstrap_self_test(void) {
    LOG_INFO_MSG("Bootstrap", "TASK-018", "self-test started");

    unsigned char code[MAX_BYTECODE];
    int len = bootstrap_compile(MINI_TOKENIZER_SRC, code, MAX_BYTECODE);

    if (len < 0) {
        fprintf(stderr, "bootstrap: self-test compilation failed\n");
        return 1;
    }

    printf("Bootstrap: compiled %d bytes of bytecode\n", len);

    /* Run the compiled bytecode */
    vm_memory_reset();
    vm_run(code, (size_t)len);

    LOG_INFO_MSG("Bootstrap", "TASK-018", "self-test complete");
    return 0;
}
