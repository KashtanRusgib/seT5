/*
 * ternary_vm.c - Ternary Virtual Machine (Setun-70 Inspired Two-Stack Model)
 *
 * Architecture:
 *   - Operand stack: expression evaluation, arithmetic, data manipulation
 *   - Return stack:  function calls, loop addresses, scope frames
 *   - Flat memory:   729 cells (3^6), ternary-addressable
 *
 * The two-stack model enforces structured programming at the execution
 * level, inspired by Setun-70's hardware support for Dijkstra's principles.
 * No unstructured GOTOs — all control flow uses stack-based nesting.
 *
 * Phase 1 (MVP): Uses int arithmetic for correctness.
 * Phase 2+: Switch to full balanced ternary (trit arrays).
 */

#include <stdio.h>
#include "../include/vm.h"
#include "../include/logger.h"

/* === Operand Stack === */
static int stack[STACK_SIZE];
static int sp = 0;

/* === Return Stack (Setun-70 inspired) === */
static int rstack[RSTACK_SIZE];
static int rsp = 0;

/* === Memory === */
static int memory[MEMORY_SIZE];
static int heap_top = MEMORY_SIZE / 2;

/* === Last result for testing === */
static int last_result = 0;

/* --- Operand stack operations --- */
static void push(int val) {
    if (sp < STACK_SIZE) stack[sp++] = val;
}

static int pop(void) {
    return (sp > 0) ? stack[--sp] : 0;
}

static int peek(void) {
    return (sp > 0) ? stack[sp - 1] : 0;
}

/* --- Return stack operations (Setun-70 two-stack model) --- */
static void rpush(int val) {
    if (rsp < RSTACK_SIZE) rstack[rsp++] = val;
}

static int rpop(void) {
    return (rsp > 0) ? rstack[--rsp] : 0;
}

static int rpeek(void) {
    return (rsp > 0) ? rstack[rsp - 1] : 0;
}

/* === Opcode name table for debugging === */
const char *opcode_names[] = {
    "PUSH", "ADD", "MUL", "JMP", "COND_JMP", "HALT",
    "LOAD", "STORE", "SUB", "SYSCALL",
    "DUP", "DROP", "SWAP", "OVER", "ROT",
    "TO_R", "FROM_R", "R_FETCH",
    "CALL", "RET", "ENTER", "LEAVE",
    "BRZ", "BRN", "BRP", "LOOP_BEGIN", "LOOP_END", "BREAK",
    "CMP_EQ", "CMP_LT", "CMP_GT",
    "NEG", "CONSENSUS", "ACCEPT_ANY",
    "PUSH_TRYTE", "PUSH_WORD"
};

/* === Public API === */

int vm_memory_read(int addr) {
    if (addr >= 0 && addr < MEMORY_SIZE) return memory[addr];
    return 0;
}

void vm_memory_write(int addr, int value) {
    if (addr >= 0 && addr < MEMORY_SIZE) memory[addr] = value;
}

void vm_memory_reset(void) {
    for (int i = 0; i < MEMORY_SIZE; i++) memory[i] = 0;
    sp = 0;
    rsp = 0;
    heap_top = MEMORY_SIZE / 2;
    last_result = 0;
}

int vm_rstack_depth(void) {
    return rsp;
}

int vm_get_result(void) {
    return last_result;
}

/* === Ternary logic helpers (trit-level, applied to int values) === */

/* Ternary negation: flip sign. For balanced ternary, this flips all trits. */
static int ternary_neg(int val) {
    return -val;
}

/* Ternary consensus (AND-like): min(a, b) per trit.
 * For int approximation: returns the value closer to zero,
 * or the more negative if both negative. */
static int ternary_consensus(int a, int b) {
    /* Trit-level consensus on the integer representation */
    trit wa[WORD_SIZE], wb[WORD_SIZE], wr[WORD_SIZE];
    int_to_trit_word(a, wa);
    int_to_trit_word(b, wb);
    for (int i = 0; i < WORD_SIZE; i++) {
        wr[i] = trit_min(wa[i], wb[i]);
    }
    return trit_word_to_int(wr);
}

/* Ternary accept-any (OR-like): max(a, b) per trit. */
static int ternary_accept_any(int a, int b) {
    trit wa[WORD_SIZE], wb[WORD_SIZE], wr[WORD_SIZE];
    int_to_trit_word(a, wa);
    int_to_trit_word(b, wb);
    for (int i = 0; i < WORD_SIZE; i++) {
        wr[i] = trit_max(wa[i], wb[i]);
    }
    return trit_word_to_int(wr);
}

/* === Main VM execution loop === */

void vm_run(unsigned char *bytecode, size_t len) {
    sp = 0;
    rsp = 0;
    LOG_DEBUG_MSG("VM", "TASK-006", "vm_run entered (two-stack model)");

    for (size_t pc = 0; pc < len; ) {
        unsigned char op = bytecode[pc++];

        switch (op) {

            /* === Phase 1: Core arithmetic & memory === */

            case OP_PUSH:
                push((int)(signed char)bytecode[pc++]);
                break;

            case OP_ADD: {
                int b = pop(), a = pop();
                push(a + b);
                break;
            }

            case OP_MUL: {
                int b = pop(), a = pop();
                push(a * b);
                break;
            }

            case OP_SUB: {
                int b = pop(), a = pop();
                push(a - b);
                break;
            }

            case OP_JMP:
                pc = (size_t)bytecode[pc];
                break;

            case OP_COND_JMP: {
                int cond = pop();
                if (cond == 0) {
                    pc = (size_t)bytecode[pc];
                } else {
                    pc++;
                }
                break;
            }

            case OP_LOAD: {
                int addr = pop();
                if (addr >= 0 && addr < MEMORY_SIZE)
                    push(memory[addr]);
                else
                    push(0);
                break;
            }

            case OP_STORE: {
                int val = pop();
                int addr = pop();
                if (addr >= 0 && addr < MEMORY_SIZE)
                    memory[addr] = val;
                break;
            }

            case OP_SYSCALL: {
                int sysno = pop();
                LOG_DEBUG_MSG("VM", "TASK-016", "syscall dispatched");
                switch (sysno) {
                    case 0: /* t_exit */
                        LOG_DEBUG_MSG("VM", "TASK-016", "t_exit");
                        return;
                    case 1: { /* t_write */
                        int fd = pop(), addr = pop(), slen = pop();
                        (void)fd; (void)addr;
                        push(slen);
                        break;
                    }
                    case 2: { /* t_read */
                        int fd = pop(), addr = pop(), slen = pop();
                        (void)fd; (void)addr; (void)slen;
                        push(0);
                        break;
                    }
                    case 3: { /* t_mmap */
                        int sz = pop();
                        int base = heap_top;
                        heap_top += sz;
                        if (heap_top > MEMORY_SIZE) heap_top = MEMORY_SIZE;
                        push(base);
                        break;
                    }
                    case 4: { /* t_cap_send */
                        int cap = pop(), msg = pop();
                        (void)cap; (void)msg;
                        push(0);
                        break;
                    }
                    case 5: { /* t_cap_recv */
                        int cap = pop();
                        (void)cap;
                        push(42);
                        break;
                    }
                    default:
                        push(-1);
                        break;
                }
                break;
            }

            case OP_HALT:
                last_result = pop();
                printf("Result: %d\n", last_result);
                LOG_DEBUG_MSG("VM", "TASK-006", "vm_run HALT");
                return;

            /* === Phase 3: Stack manipulation (Setun-70 postfix) === */

            case OP_DUP: {
                int val = peek();
                push(val);
                break;
            }

            case OP_DROP:
                pop();
                break;

            case OP_SWAP: {
                int b = pop(), a = pop();
                push(b);
                push(a);
                break;
            }

            case OP_OVER: {
                int b = pop(), a = pop();
                push(a);
                push(b);
                push(a);
                break;
            }

            case OP_ROT: {
                int c = pop(), b = pop(), a = pop();
                push(b);
                push(c);
                push(a);
                break;
            }

            /* === Phase 3: Return stack ops (two-stack model) === */

            case OP_TO_R:
                rpush(pop());
                break;

            case OP_FROM_R:
                push(rpop());
                break;

            case OP_R_FETCH:
                push(rpeek());
                break;

            /* === Phase 3: Function call convention === */

            case OP_CALL: {
                /* Push return address (PC after addr byte) to return stack */
                size_t target = (size_t)bytecode[pc++];
                rpush((int)(pc));  /* return to instruction after CALL */
                pc = target;
                break;
            }

            case OP_RET: {
                /* Pop return address from return stack, continue there */
                int ret_addr = rpop();
                pc = (size_t)ret_addr;
                break;
            }

            case OP_ENTER:
                /* Push frame marker (-1 sentinel) to return stack */
                rpush(-1);
                break;

            case OP_LEAVE:
                /* Pop return stack until frame marker (-1) */
                while (rsp > 0 && rpeek() != -1) {
                    rpop();
                }
                if (rsp > 0) rpop(); /* pop the marker itself */
                break;

            /* === Phase 3: Structured control flow (DSSP-style) === */

            case OP_BRZ: {
                /* Branch if zero: pop TOS, if 0 skip to addr, else continue */
                int cond = pop();
                if (cond == 0) {
                    pc = (size_t)bytecode[pc];
                } else {
                    pc++; /* skip addr byte */
                }
                break;
            }

            case OP_BRN: {
                /* Branch if negative */
                int cond = pop();
                if (cond < 0) {
                    pc = (size_t)bytecode[pc];
                } else {
                    pc++;
                }
                break;
            }

            case OP_BRP: {
                /* Branch if positive */
                int cond = pop();
                if (cond > 0) {
                    pc = (size_t)bytecode[pc];
                } else {
                    pc++;
                }
                break;
            }

            case OP_LOOP_BEGIN:
                /* Push current PC (loop body start) to return stack */
                rpush((int)pc);
                break;

            case OP_LOOP_END: {
                /* Pop condition; if !=0, jump back to loop start (rstack TOS) */
                int cond = pop();
                if (cond != 0) {
                    pc = (size_t)rpeek(); /* jump to loop start */
                } else {
                    rpop(); /* done: remove loop addr from return stack */
                }
                break;
            }

            case OP_BREAK:
                /* Exit loop: pop loop address from return stack, skip to end */
                if (rsp > 0) rpop();
                /* Scan forward for matching LOOP_END */
                while (pc < len && bytecode[pc] != OP_LOOP_END) {
                    /* Skip operand bytes for opcodes that have them */
                    unsigned char skip_op = bytecode[pc++];
                    if (skip_op == OP_PUSH || skip_op == OP_JMP ||
                        skip_op == OP_COND_JMP || skip_op == OP_BRZ ||
                        skip_op == OP_BRN || skip_op == OP_BRP ||
                        skip_op == OP_CALL || skip_op == OP_PUSH_TRYTE) {
                        pc++; /* skip 1-byte operand */
                    } else if (skip_op == OP_PUSH_WORD) {
                        pc += 2; /* skip 2-byte operand */
                    }
                }
                if (pc < len) pc++; /* skip past LOOP_END itself */
                break;

            /* === Phase 3: Comparison ops === */

            case OP_CMP_EQ: {
                int b = pop(), a = pop();
                push(a == b ? 1 : 0);
                break;
            }

            case OP_CMP_LT: {
                /* Ternary comparison: returns -1, 0, or 1 */
                int b = pop(), a = pop();
                push(a < b ? 1 : (a > b ? -1 : 0));
                break;
            }

            case OP_CMP_GT: {
                int b = pop(), a = pop();
                push(a > b ? 1 : (a < b ? -1 : 0));
                break;
            }

            /* === Phase 3: Ternary logic gates === */

            case OP_NEG: {
                int val = pop();
                push(ternary_neg(val));
                break;
            }

            case OP_CONSENSUS: {
                int b = pop(), a = pop();
                push(ternary_consensus(a, b));
                break;
            }

            case OP_ACCEPT_ANY: {
                int b = pop(), a = pop();
                push(ternary_accept_any(a, b));
                break;
            }

            /* === Phase 3: Extended data === */

            case OP_PUSH_TRYTE: {
                /* Read 1-byte tryte index, convert 6-trit value */
                int idx = (int)(signed char)bytecode[pc++];
                push(idx);  /* Phase 1: treat as integer */
                break;
            }

            case OP_PUSH_WORD: {
                /* Read 2-byte packed 9-trit word value */
                int lo = (int)(unsigned char)bytecode[pc++];
                int hi = (int)(signed char)bytecode[pc++];
                push((hi << 8) | lo);
                break;
            }

            default:
                fprintf(stderr, "VM: unknown opcode %d at pc=%zu\n",
                        op, pc - 1);
                return;
        }
    }
}
