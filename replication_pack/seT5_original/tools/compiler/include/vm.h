#ifndef VM_H
#define VM_H

#include "ternary.h"
#include <stddef.h>

/*
 * Ternary VM Architecture — Setun-70 Inspired
 *
 * Two-stack model (inspired by Setun-70/DSSP):
 *   - Operand stack: data manipulation, expression evaluation
 *   - Return stack:  control flow, function calls, nested blocks
 *
 * This enforces structured programming (Dijkstra/Brusentsov) at the
 * hardware level — no unstructured jumps required for if/while/for.
 *
 * Memory is ternary-addressable: 3^6 = 729 cells (expandable to 3^9).
 * Instructions use 6-trit tryte-aligned syllables where practical.
 */

#define STACK_SIZE      256
#define RSTACK_SIZE     256   /* Return stack depth (nested calls/blocks) */
#define MEMORY_SIZE     729   /* 3^6 = 729 ternary-addressable cells */

/*
 * ISA Opcodes — Setun-70/DSSP inspired instruction set
 *
 * Phase 1 (MVP):     OP_PUSH..OP_SYSCALL (original 10 opcodes)
 * Phase 3 (Setun70): Structured control flow, two-stack ops,
 *                    ternary logic, function call convention
 */
enum Opcode {
    /* === Phase 1: Core arithmetic & memory === */
    OP_PUSH,        /*  0: Push next byte (sign-extended) onto operand stack */
    OP_ADD,         /*  1: Pop b, a; push a+b */
    OP_MUL,         /*  2: Pop b, a; push a*b */
    OP_JMP,         /*  3: Set PC to next byte (absolute jump) */
    OP_COND_JMP,    /*  4: Pop cond; if cond==0, jump to next byte */
    OP_HALT,        /*  5: Pop TOS, print result, halt */
    OP_LOAD,        /*  6: Pop addr, push memory[addr] */
    OP_STORE,       /*  7: Pop value, pop addr; memory[addr] = value */
    OP_SUB,         /*  8: Pop b, a; push a-b */
    OP_SYSCALL,     /*  9: Pop sysno, dispatch per seT5 ABI */

    /* === Phase 3: Stack manipulation (Setun-70 postfix style) === */
    OP_DUP,         /* 10: Duplicate TOS: ( a -- a a ) */
    OP_DROP,        /* 11: Discard TOS:   ( a -- ) */
    OP_SWAP,        /* 12: Swap top two:  ( a b -- b a ) */
    OP_OVER,        /* 13: Copy NOS:      ( a b -- a b a ) */
    OP_ROT,         /* 14: Rotate third:  ( a b c -- b c a ) */

    /* === Phase 3: Return stack ops (Setun-70 two-stack model) === */
    OP_TO_R,        /* 15: Move TOS to return stack: ( a -- ) (R: -- a) */
    OP_FROM_R,      /* 16: Move return stack TOS to operand stack */
    OP_R_FETCH,     /* 17: Copy return stack TOS without popping */

    /* === Phase 3: Function call convention === */
    OP_CALL,        /* 18: Push PC+2 to return stack, jump to addr */
    OP_RET,         /* 19: Pop return stack, set PC */
    OP_ENTER,       /* 20: Enter scope — push frame marker to return stack */
    OP_LEAVE,       /* 21: Leave scope — pop back to frame marker */

    /* === Phase 3: Structured control flow (DSSP-style) === */
    OP_BRZ,         /* 22: Branch if TOS == 0 (pop, skip next word if zero) */
    OP_BRN,         /* 23: Branch if TOS < 0 (negative) */
    OP_BRP,         /* 24: Branch if TOS > 0 (positive) */
    OP_LOOP_BEGIN,  /* 25: Push loop-start addr on return stack */
    OP_LOOP_END,    /* 26: Pop cond; if != 0, jump to return stack TOS */
    OP_BREAK,       /* 27: Pop return stack (loop addr), skip to matching end */

    /* === Phase 3: Comparison ops === */
    OP_CMP_EQ,      /* 28: Pop b, a; push (a==b ? 1 : 0) */
    OP_CMP_LT,      /* 29: Pop b, a; push (a<b ? 1 : -1 if a>b : 0) */
    OP_CMP_GT,      /* 30: Pop b, a; push (a>b ? 1 : -1 if a<b : 0) */

    /* === Phase 3: Ternary logic gates (Brusentsov/Jones) === */
    OP_NEG,         /* 31: Ternary negation: flip all trits (-1↔1, 0→0) */
    OP_CONSENSUS,   /* 32: Ternary AND (trit_min): pop b, a; push min(a,b) */
    OP_ACCEPT_ANY,  /* 33: Ternary OR  (trit_max): pop b, a; push max(a,b) */

    /* === Phase 3: Extended data === */
    OP_PUSH_TRYTE,  /* 34: Push 6-trit tryte value (next byte = tryte index) */
    OP_PUSH_WORD,   /* 35: Push 9-trit word (next 2 bytes = packed value) */

    OP_COUNT        /* Sentinel: total opcode count */
};

/*
 * Opcode names for disassembly/debugging
 */
extern const char *opcode_names[];

/* Run bytecode on the ternary VM (two-stack model) */
void vm_run(unsigned char *bytecode, size_t len);

/* Memory access for tests */
int vm_memory_read(int addr);
void vm_memory_write(int addr, int value);
void vm_memory_reset(void);

/* Return stack inspection for tests/debugging */
int vm_rstack_depth(void);

/* Get last execution result (TOS at halt) */
int vm_get_result(void);

#endif
