/*
 * postfix_ir.h - Postfix IR (POLIZ-style, Setun-70 Inspired)
 *
 * Converts AST to a flat postfix instruction sequence for peephole
 * optimization. Inspired by Setun-70's POLIZ autocode and DSSP's
 * postfix evaluation model.
 *
 * The postfix IR is a linear sequence of typed instructions that
 * can be directly translated to ternary bytecode. It bridges
 * the gap between tree-shaped AST and flat bytecode, enabling:
 *   - Peephole optimizations (combine mul+add, eliminate redundant ops)
 *   - Structured control flow verification (no unstructured jumps)
 *   - Easy debugging (human-readable instruction dump)
 */

#ifndef POSTFIX_IR_H
#define POSTFIX_IR_H

#include "ir.h"

/* Postfix instruction types */
typedef enum {
    PF_PUSH_CONST,      /* Push integer constant */
    PF_PUSH_VAR,        /* Push variable (load from memory) */
    PF_STORE_VAR,       /* Store to variable */
    PF_ADD,             /* a + b */
    PF_SUB,             /* a - b */
    PF_MUL,             /* a * b */
    PF_CMP_EQ,          /* a == b */
    PF_CMP_LT,          /* a < b */
    PF_CMP_GT,          /* a > b */
    PF_NEG,             /* Ternary negation */
    PF_CONSENSUS,       /* Ternary AND (min) */
    PF_ACCEPT_ANY,      /* Ternary OR (max) */
    PF_BRZ,             /* Branch if zero (offset) */
    PF_BRN,             /* Branch if negative (offset) */
    PF_BRP,             /* Branch if positive (offset) */
    PF_JMP,             /* Unconditional jump (offset) */
    PF_LOOP_BEGIN,      /* Loop start marker */
    PF_LOOP_END,        /* Loop end (branch back if nonzero) */
    PF_CALL,            /* Function call */
    PF_RET,             /* Return */
    PF_ENTER,           /* Enter scope (push frame) */
    PF_LEAVE,           /* Leave scope (pop frame) */
    PF_DEREF,           /* Pointer dereference */
    PF_ADDR_OF,         /* Address-of */
    PF_DUP,             /* Duplicate TOS */
    PF_DROP,            /* Drop TOS */
    PF_HALT,            /* Halt execution */
    PF_NOP,             /* No operation (placeholder) */
    PF_LABEL            /* Label (target for jumps, not emitted) */
} PostfixOp;

/* Single postfix instruction */
typedef struct {
    PostfixOp op;
    int operand;        /* For PUSH_CONST: value; for BRZ/JMP: target index;
                           for PUSH_VAR/STORE_VAR: var offset; for LABEL: label id */
    char *name;         /* For PUSH_VAR/STORE_VAR/CALL: variable/function name */
} PostfixInstr;

/* Postfix instruction sequence */
typedef struct {
    PostfixInstr *instrs;
    int count;
    int capacity;
    int next_label;     /* Label counter for control flow */
} PostfixSeq;

/* Initialize a postfix sequence */
void pf_init(PostfixSeq *seq);

/* Free a postfix sequence */
void pf_free(PostfixSeq *seq);

/* Emit one instruction to the sequence */
void pf_emit(PostfixSeq *seq, PostfixOp op, int operand, const char *name);

/* Allocate a new label and return its id */
int pf_alloc_label(PostfixSeq *seq);

/* Find the index of a label in the sequence */
int pf_find_label(PostfixSeq *seq, int label_id);

/* Convert an AST to a postfix instruction sequence */
void pf_from_ast(PostfixSeq *seq, Expr *ast);

/* Peephole optimization pass on postfix IR */
void pf_optimize(PostfixSeq *seq);

/* Dump postfix IR for debugging */
void pf_dump(const PostfixSeq *seq);

#endif /* POSTFIX_IR_H */
