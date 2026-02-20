/*
 * postfix_ir.c - Postfix IR Implementation (POLIZ-style, Setun-70 Inspired)
 *
 * Converts AST to a flat postfix instruction sequence. This mirrors
 * Setun-70's POLIZ autocode, where expressions are evaluated in
 * reverse Polish notation using a stack machine.
 *
 * The postfix IR enables:
 *   1. Peephole optimizations before bytecode emission
 *   2. Linear instruction stream for structured control flow
 *   3. Easy translation to ternary VM bytecode
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/postfix_ir.h"

void pf_init(PostfixSeq *seq) {
    seq->capacity = 64;
    seq->count = 0;
    seq->next_label = 0;
    seq->instrs = (PostfixInstr *)malloc(seq->capacity * sizeof(PostfixInstr));
    if (!seq->instrs) {
        fprintf(stderr, "postfix_ir: malloc failed\n");
        exit(1);
    }
}

void pf_free(PostfixSeq *seq) {
    if (seq->instrs) {
        for (int i = 0; i < seq->count; i++) {
            if (seq->instrs[i].name) free(seq->instrs[i].name);
        }
        free(seq->instrs);
    }
    seq->instrs = NULL;
    seq->count = 0;
    seq->capacity = 0;
}

void pf_emit(PostfixSeq *seq, PostfixOp op, int operand, const char *name) {
    if (seq->count >= seq->capacity) {
        seq->capacity *= 2;
        seq->instrs = (PostfixInstr *)realloc(seq->instrs,
            seq->capacity * sizeof(PostfixInstr));
        if (!seq->instrs) {
            fprintf(stderr, "postfix_ir: realloc failed\n");
            exit(1);
        }
    }
    PostfixInstr *instr = &seq->instrs[seq->count++];
    instr->op = op;
    instr->operand = operand;
    instr->name = name ? strdup(name) : NULL;
}

int pf_alloc_label(PostfixSeq *seq) {
    return seq->next_label++;
}

int pf_find_label(PostfixSeq *seq, int label_id) {
    for (int i = 0; i < seq->count; i++) {
        if (seq->instrs[i].op == PF_LABEL && seq->instrs[i].operand == label_id) {
            return i;
        }
    }
    return -1;
}

/* --- AST to postfix conversion --- */

static void emit_ast(PostfixSeq *seq, Expr *e) {
    if (e == NULL) return;

    switch (e->type) {
        case NODE_CONST:
            pf_emit(seq, PF_PUSH_CONST, e->val, NULL);
            break;

        case NODE_VAR:
            pf_emit(seq, PF_PUSH_VAR, 0, e->name);
            break;

        case NODE_BINOP:
            emit_ast(seq, e->left);
            emit_ast(seq, e->right);
            switch (e->op) {
                case OP_IR_ADD:    pf_emit(seq, PF_ADD, 0, NULL); break;
                case OP_IR_SUB:    pf_emit(seq, PF_SUB, 0, NULL); break;
                case OP_IR_MUL:    pf_emit(seq, PF_MUL, 0, NULL); break;
                case OP_IR_CMP_EQ: pf_emit(seq, PF_CMP_EQ, 0, NULL); break;
                case OP_IR_CMP_LT: pf_emit(seq, PF_CMP_LT, 0, NULL); break;
                case OP_IR_CMP_GT: pf_emit(seq, PF_CMP_GT, 0, NULL); break;
                case OP_IR_NEG:    pf_emit(seq, PF_NEG, 0, NULL); break;
            }
            break;

        case NODE_RETURN:
            emit_ast(seq, e->left);
            pf_emit(seq, PF_RET, 0, NULL);
            break;

        case NODE_VAR_DECL:
            if (e->left) emit_ast(seq, e->left);
            pf_emit(seq, PF_STORE_VAR, 0, e->name);
            break;

        case NODE_ASSIGN:
            emit_ast(seq, e->right);
            if (e->left && e->left->type == NODE_VAR) {
                pf_emit(seq, PF_STORE_VAR, 0, e->left->name);
            }
            break;

        case NODE_DEREF:
            emit_ast(seq, e->left);
            pf_emit(seq, PF_DEREF, 0, NULL);
            break;

        case NODE_ADDR_OF:
            if (e->left && e->left->type == NODE_VAR)
                pf_emit(seq, PF_ADDR_OF, 0, e->left->name);
            break;

        case NODE_FUNC_CALL:
            /* Push args in order, then call */
            for (int i = 0; i < e->param_count; i++) {
                emit_ast(seq, e->params[i]);
            }
            pf_emit(seq, PF_CALL, e->param_count, e->name);
            break;

        case NODE_FUNC_DEF:
            pf_emit(seq, PF_ENTER, 0, e->name);
            /* Emit preceding statements (stored in params after the formal params) */
            for (int i = 0; i < e->param_count; i++) {
                emit_ast(seq, e->params[i]);
            }
            emit_ast(seq, e->body);
            pf_emit(seq, PF_LEAVE, 0, e->name);
            break;

        case NODE_PROGRAM:
            for (int i = 0; i < e->param_count; i++) {
                emit_ast(seq, e->params[i]);
            }
            pf_emit(seq, PF_HALT, 0, NULL);
            break;

        case NODE_IF: {
            /* Setun-70 style: eval cond, branch if zero (skip body) */
            int lbl_else = pf_alloc_label(seq);
            int lbl_end = pf_alloc_label(seq);

            emit_ast(seq, e->condition);
            pf_emit(seq, PF_BRZ, lbl_else, NULL);

            /* then branch */
            emit_ast(seq, e->body);
            if (e->else_body) {
                pf_emit(seq, PF_JMP, lbl_end, NULL);
            }

            pf_emit(seq, PF_LABEL, lbl_else, NULL);

            if (e->else_body) {
                emit_ast(seq, e->else_body);
                pf_emit(seq, PF_LABEL, lbl_end, NULL);
            }
            break;
        }

        case NODE_WHILE: {
            /* Structured loop using LOOP_BEGIN/END (Setun-70 return stack) */
            int lbl_start = pf_alloc_label(seq);
            int lbl_end = pf_alloc_label(seq);

            pf_emit(seq, PF_LABEL, lbl_start, NULL);
            pf_emit(seq, PF_LOOP_BEGIN, 0, NULL);

            emit_ast(seq, e->condition);
            pf_emit(seq, PF_BRZ, lbl_end, NULL);

            emit_ast(seq, e->body);

            /* Loop continuation: push nonzero for LOOP_END */
            pf_emit(seq, PF_PUSH_CONST, 1, NULL);
            pf_emit(seq, PF_LOOP_END, 0, NULL);

            pf_emit(seq, PF_LABEL, lbl_end, NULL);
            break;
        }

        case NODE_FOR: {
            /* for (init; cond; inc) { body }
             * -> init; LOOP_BEGIN; cond; BRZ end; body; inc; 1; LOOP_END; end: */
            int lbl_start = pf_alloc_label(seq);
            int lbl_end = pf_alloc_label(seq);

            emit_ast(seq, e->left);  /* init */

            pf_emit(seq, PF_LABEL, lbl_start, NULL);
            pf_emit(seq, PF_LOOP_BEGIN, 0, NULL);

            emit_ast(seq, e->condition);  /* cond */
            pf_emit(seq, PF_BRZ, lbl_end, NULL);

            emit_ast(seq, e->body);       /* body */
            emit_ast(seq, e->increment);  /* inc */

            pf_emit(seq, PF_PUSH_CONST, 1, NULL);
            pf_emit(seq, PF_LOOP_END, 0, NULL);

            pf_emit(seq, PF_LABEL, lbl_end, NULL);
            break;
        }

        case NODE_BLOCK:
            for (int i = 0; i < e->param_count; i++) {
                emit_ast(seq, e->params[i]);
            }
            break;

        /* Phase 3: Arrays */
        case NODE_ARRAY_DECL:
            /* Emit initializers as STORE_VAR with computed names */
            for (int i = 0; i < e->param_count; i++) {
                emit_ast(seq, e->params[i]);
                char slotname[72];
                snprintf(slotname, sizeof(slotname), "%s[%d]", e->name, i);
                pf_emit(seq, PF_STORE_VAR, i, slotname);
            }
            break;

        case NODE_ARRAY_ACCESS:
            /* Push base + index, deref */
            pf_emit(seq, PF_PUSH_VAR, 0, e->name);
            emit_ast(seq, e->left);
            pf_emit(seq, PF_ADD, 0, NULL);
            pf_emit(seq, PF_DEREF, 0, NULL);
            break;

        case NODE_ARRAY_ASSIGN:
            /* Compute address, compute value, store */
            pf_emit(seq, PF_PUSH_VAR, 0, e->name);
            emit_ast(seq, e->left);
            pf_emit(seq, PF_ADD, 0, NULL);
            emit_ast(seq, e->right);
            pf_emit(seq, PF_STORE_VAR, 0, e->name);
            break;

        case NODE_TRIT_VAR_DECL:
            if (e->left) emit_ast(seq, e->left);
            pf_emit(seq, PF_STORE_VAR, 0, e->name);
            break;

        case NODE_TRIT_ARRAY_DECL:
            /* Emit initializers as STORE_VAR with computed names */
            for (int i = 0; i < e->param_count; i++) {
                emit_ast(seq, e->params[i]);
                char slotname[72];
                snprintf(slotname, sizeof(slotname), "%s[%d]", e->name, i);
                pf_emit(seq, PF_STORE_VAR, i, slotname);
            }
            break;
    }
}

void pf_from_ast(PostfixSeq *seq, Expr *ast) {
    emit_ast(seq, ast);
}

/* --- Peephole optimization --- */

void pf_optimize(PostfixSeq *seq) {
    /*
     * Peephole patterns inspired by Setun-70's compact instruction design:
     *
     * 1. PUSH 0, ADD -> NOP (identity: a + 0 = a)
     * 2. PUSH 1, MUL -> NOP (identity: a * 1 = a)
     * 3. PUSH 0, MUL -> DROP, PUSH 0 (zero: a * 0 = 0)
     * 4. DUP, DROP -> NOP (redundant stack ops)
     * 5. Two consecutive PUSH_CONST + arithmetic -> fold to one PUSH_CONST
     */
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < seq->count - 1; i++) {
            PostfixInstr *a = &seq->instrs[i];
            PostfixInstr *b = &seq->instrs[i + 1];

            /* Pattern: PUSH_CONST 0, ADD -> NOP both */
            if (a->op == PF_PUSH_CONST && a->operand == 0 && b->op == PF_ADD) {
                a->op = PF_NOP;
                b->op = PF_NOP;
                changed = 1;
            }
            /* Pattern: PUSH_CONST 1, MUL -> NOP both */
            else if (a->op == PF_PUSH_CONST && a->operand == 1 && b->op == PF_MUL) {
                a->op = PF_NOP;
                b->op = PF_NOP;
                changed = 1;
            }
            /* Pattern: PUSH_CONST 0, MUL -> DROP prev, PUSH 0 */
            else if (a->op == PF_PUSH_CONST && a->operand == 0 && b->op == PF_MUL) {
                a->op = PF_DROP;
                b->op = PF_PUSH_CONST;
                b->operand = 0;
                changed = 1;
            }
            /* Pattern: Two PUSH_CONST + ADD -> fold */
            if (i >= 1) {
                PostfixInstr *prev = &seq->instrs[i - 1];
                if (prev->op == PF_PUSH_CONST && a->op == PF_PUSH_CONST &&
                    b->op == PF_ADD) {
                    prev->operand = prev->operand + a->operand;
                    a->op = PF_NOP;
                    b->op = PF_NOP;
                    changed = 1;
                }
                else if (prev->op == PF_PUSH_CONST && a->op == PF_PUSH_CONST &&
                         b->op == PF_MUL) {
                    prev->operand = prev->operand * a->operand;
                    a->op = PF_NOP;
                    b->op = PF_NOP;
                    changed = 1;
                }
                else if (prev->op == PF_PUSH_CONST && a->op == PF_PUSH_CONST &&
                         b->op == PF_SUB) {
                    prev->operand = prev->operand - a->operand;
                    a->op = PF_NOP;
                    b->op = PF_NOP;
                    changed = 1;
                }
            }
        }

        /* Compact: remove NOPs */
        if (changed) {
            int write = 0;
            for (int read = 0; read < seq->count; read++) {
                if (seq->instrs[read].op != PF_NOP) {
                    if (write != read) {
                        seq->instrs[write] = seq->instrs[read];
                    }
                    write++;
                } else {
                    if (seq->instrs[read].name) free(seq->instrs[read].name);
                }
            }
            seq->count = write;
        }
    }
}

/* --- Dump --- */

static const char *pf_op_names[] = {
    "PUSH_CONST", "PUSH_VAR", "STORE_VAR",
    "ADD", "SUB", "MUL",
    "CMP_EQ", "CMP_LT", "CMP_GT",
    "NEG", "CONSENSUS", "ACCEPT_ANY",
    "BRZ", "BRN", "BRP", "JMP",
    "LOOP_BEGIN", "LOOP_END",
    "CALL", "RET",
    "ENTER", "LEAVE",
    "DEREF", "ADDR_OF",
    "DUP", "DROP",
    "HALT", "NOP", "LABEL"
};

void pf_dump(const PostfixSeq *seq) {
    printf("--- Postfix IR (%d instructions) ---\n", seq->count);
    for (int i = 0; i < seq->count; i++) {
        const PostfixInstr *instr = &seq->instrs[i];
        printf("  %3d: %-12s", i, pf_op_names[instr->op]);
        if (instr->op == PF_PUSH_CONST) {
            printf(" %d", instr->operand);
        } else if (instr->op == PF_LABEL) {
            printf(" L%d", instr->operand);
        } else if (instr->op == PF_BRZ || instr->op == PF_BRN ||
                   instr->op == PF_BRP || instr->op == PF_JMP) {
            printf(" -> L%d", instr->operand);
        } else if (instr->name) {
            printf(" %s", instr->name);
        }
        printf("\n");
    }
    printf("---\n");
}
