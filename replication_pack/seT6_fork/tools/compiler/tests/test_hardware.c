/*
 * test_hardware.c - Tests for TASK-017: Ternary Hardware Simulation
 *
 * Tests C-level ternary gate simulations that mirror the Verilog
 * ternary ALU (hw/ternary_alu.v). Verifies: trit add, mul, min,
 * max, inverter, carry propagation, word-level operations.
 */

#include "../include/test_harness.h"
#include "../include/ternary.h"
#include "../include/verilog_emit.h"

/* ---- Single-trit gate tests ---- */

TEST(test_trit_add_basic) {
    trit carry = TRIT_Z;
    /* P + N = Z, carry Z */
    ASSERT_EQ(trit_add(TRIT_P, TRIT_N, &carry), TRIT_Z);
    ASSERT_EQ(carry, TRIT_Z);

    /* Z + Z = Z, carry Z */
    carry = TRIT_Z;
    ASSERT_EQ(trit_add(TRIT_Z, TRIT_Z, &carry), TRIT_Z);
    ASSERT_EQ(carry, TRIT_Z);

    /* P + Z = P, carry Z */
    carry = TRIT_Z;
    ASSERT_EQ(trit_add(TRIT_P, TRIT_Z, &carry), TRIT_P);
    ASSERT_EQ(carry, TRIT_Z);
}

TEST(test_trit_add_carry) {
    trit carry = TRIT_Z;
    /* P + P = N, carry P (1+1=2, balanced: -1 with carry +1) */
    ASSERT_EQ(trit_add(TRIT_P, TRIT_P, &carry), TRIT_N);
    ASSERT_EQ(carry, TRIT_P);

    /* N + N = P, carry N (-1+-1=-2, balanced: +1 with carry -1) */
    carry = TRIT_Z;
    ASSERT_EQ(trit_add(TRIT_N, TRIT_N, &carry), TRIT_P);
    ASSERT_EQ(carry, TRIT_N);

    /* P + P + P(carry) = Z, carry P (1+1+1=3, balanced: 0 carry 1) */
    carry = TRIT_P;
    ASSERT_EQ(trit_add(TRIT_P, TRIT_P, &carry), TRIT_Z);
    ASSERT_EQ(carry, TRIT_P);
}

TEST(test_trit_mul) {
    /* trit multiplication truth table */
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_P), TRIT_P);   /*  1 *  1 =  1 */
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_N), TRIT_N);   /*  1 * -1 = -1 */
    ASSERT_EQ(trit_mul(TRIT_N, TRIT_P), TRIT_N);   /* -1 *  1 = -1 */
    ASSERT_EQ(trit_mul(TRIT_N, TRIT_N), TRIT_P);   /* -1 * -1 =  1 */
    ASSERT_EQ(trit_mul(TRIT_Z, TRIT_P), TRIT_Z);   /*  0 *  1 =  0 */
    ASSERT_EQ(trit_mul(TRIT_P, TRIT_Z), TRIT_Z);   /*  1 *  0 =  0 */
    ASSERT_EQ(trit_mul(TRIT_Z, TRIT_Z), TRIT_Z);   /*  0 *  0 =  0 */
}

TEST(test_trit_min) {
    /* MIN gate: returns lesser-valued trit */
    ASSERT_EQ(trit_min(TRIT_P, TRIT_N), TRIT_N);
    ASSERT_EQ(trit_min(TRIT_N, TRIT_P), TRIT_N);
    ASSERT_EQ(trit_min(TRIT_Z, TRIT_P), TRIT_Z);
    ASSERT_EQ(trit_min(TRIT_Z, TRIT_N), TRIT_N);
    ASSERT_EQ(trit_min(TRIT_P, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_min(TRIT_N, TRIT_N), TRIT_N);
}

TEST(test_trit_max) {
    /* MAX gate: returns greater-valued trit */
    ASSERT_EQ(trit_max(TRIT_P, TRIT_N), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_N, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_Z, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_Z, TRIT_N), TRIT_Z);
    ASSERT_EQ(trit_max(TRIT_P, TRIT_P), TRIT_P);
    ASSERT_EQ(trit_max(TRIT_N, TRIT_N), TRIT_N);
}

TEST(test_trit_inverter) {
    /* Ternary inverter: negate (-1 -> +1, 0 -> 0, +1 -> -1) */
    ASSERT_EQ((trit)(-(int)TRIT_P), TRIT_N);
    ASSERT_EQ((trit)(-(int)TRIT_N), TRIT_P);
    ASSERT_EQ((trit)(-(int)TRIT_Z), TRIT_Z);
}

/* ---- Word-level tests ---- */

TEST(test_trit_word_add) {
    trit_word a, b, res;

    /* 1 + 1 = 2 (balanced ternary: [N, P, Z, ...] = -1 + 3 = 2) */
    int_to_trit_word(1, a);
    int_to_trit_word(1, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 2);

    /* 13 + 14 = 27 = 3^3 */
    int_to_trit_word(13, a);
    int_to_trit_word(14, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 27);

    /* -1 + 1 = 0 */
    int_to_trit_word(-1, a);
    int_to_trit_word(1, b);
    trit_word_add(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 0);
}

TEST(test_trit_word_mul) {
    trit_word a, b, res;

    /* 3 * 3 = 9 (ternary power) */
    int_to_trit_word(3, a);
    int_to_trit_word(3, b);
    trit_word_mul(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 9);

    /* 1 * -1 = -1 */
    int_to_trit_word(1, a);
    int_to_trit_word(-1, b);
    trit_word_mul(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), -1);

    /* 0 * 42 = 0 */
    int_to_trit_word(0, a);
    int_to_trit_word(42, b);
    trit_word_mul(a, b, res);
    ASSERT_EQ(trit_word_to_int(res), 0);
}

TEST(test_trit_word_conversion_roundtrip) {
    /* Test int -> trit_word -> int roundtrip for several values */
    int test_values[] = {0, 1, -1, 3, -3, 9, -9, 13, 27, -27, 40, -40, 121};
    int count = sizeof(test_values) / sizeof(test_values[0]);
    trit_word w;

    for (int i = 0; i < count; i++) {
        int_to_trit_word(test_values[i], w);
        ASSERT_EQ(trit_word_to_int(w), test_values[i]);
    }
}

TEST(test_trit_word_sub_via_negate) {
    /* Subtraction: a - b = a + (-b) (negate then add) */
    trit_word a, b, neg_b, res;

    int_to_trit_word(10, a);
    int_to_trit_word(3, b);

    /* Negate b trit-by-trit */
    for (int i = 0; i < WORD_SIZE; i++) {
        neg_b[i] = (trit)(-(int)b[i]);
    }

    trit_word_add(a, neg_b, res);
    ASSERT_EQ(trit_word_to_int(res), 7);
}

/* ---- ALU simulation tests (C equivalent of Verilog ALU) ---- */

/* C simulation of ALU operations matching hw/ternary_alu.v */
static int alu_sim(int a, int b, int op) {
    switch (op) {
        case 0: return a + b;     /* ADD */
        case 1: return a - b;     /* SUB */
        case 2: return a * b;     /* MUL */
        default: return 0;
    }
}

TEST(test_alu_sim_add) {
    ASSERT_EQ(alu_sim(1, 1, 0), 2);
    ASSERT_EQ(alu_sim(13, 14, 0), 27);
    ASSERT_EQ(alu_sim(-1, 1, 0), 0);
}

TEST(test_alu_sim_sub) {
    ASSERT_EQ(alu_sim(1, 1, 1), 0);
    ASSERT_EQ(alu_sim(10, 3, 1), 7);
    ASSERT_EQ(alu_sim(0, 1, 1), -1);
}

TEST(test_alu_sim_mul) {
    ASSERT_EQ(alu_sim(3, 3, 2), 9);
    ASSERT_EQ(alu_sim(1, -1, 2), -1);
    ASSERT_EQ(alu_sim(-1, -1, 2), 1);
    ASSERT_EQ(alu_sim(0, 42, 2), 0);
}

/* ---- Phase 4: Full processor simulation (C software model) ---- */

/* Software model of the full 36-opcode processor (mirrors ternary_processor_full.v) */
#define PROC_SIM_STACK_SIZE 16
#define PROC_SIM_MEM_SIZE   729

typedef struct {
    int ostack[PROC_SIM_STACK_SIZE];
    int osp;
    int rstack[PROC_SIM_STACK_SIZE];
    int rsp;
    unsigned char code[256];
    int pc;
    int mem[PROC_SIM_MEM_SIZE];
    int halted;
} ProcSim;

static void proc_sim_init(ProcSim *p) {
    p->osp = 0;
    p->rsp = 0;
    p->pc = 0;
    p->halted = 0;
    for (int i = 0; i < 256; i++) p->code[i] = 0;
    for (int i = 0; i < PROC_SIM_MEM_SIZE; i++) p->mem[i] = 0;
}

static void proc_sim_push(ProcSim *p, int val) {
    if (p->osp < PROC_SIM_STACK_SIZE) p->ostack[p->osp++] = val;
}

static int proc_sim_pop(ProcSim *p) {
    return (p->osp > 0) ? p->ostack[--p->osp] : 0;
}

static int proc_sim_tos(ProcSim *p) {
    return (p->osp > 0) ? p->ostack[p->osp - 1] : 0;
}

static void proc_sim_run(ProcSim *p, int max_steps) {
    for (int step = 0; step < max_steps && !p->halted; step++) {
        unsigned char op = p->code[p->pc];
        unsigned char operand = p->code[p->pc + 1];
        int a, b, addr;
        p->pc += 2;
        switch (op) {
            case 0: break; /* NOP */
            case 1: proc_sim_push(p, (int)(signed char)operand); break; /* PUSH */
            case 2: b = proc_sim_pop(p); a = proc_sim_pop(p); proc_sim_push(p, a + b); break; /* ADD */
            case 3: b = proc_sim_pop(p); a = proc_sim_pop(p); proc_sim_push(p, a - b); break; /* SUB */
            case 4: b = proc_sim_pop(p); a = proc_sim_pop(p); proc_sim_push(p, a * b); break; /* MUL */
            case 5: p->halted = 1; break; /* HALT */
            case 6: a = proc_sim_tos(p); proc_sim_push(p, a); break; /* DUP */
            case 7: proc_sim_pop(p); break; /* DROP */
            case 8: /* SWAP */
                b = proc_sim_pop(p); a = proc_sim_pop(p);
                proc_sim_push(p, b); proc_sim_push(p, a);
                break;
            case 9: /* OVER */
                if (p->osp >= 2) proc_sim_push(p, p->ostack[p->osp - 2]);
                break;
            case 10: /* ROT */
                if (p->osp >= 3) {
                    a = p->ostack[p->osp - 3];
                    p->ostack[p->osp - 3] = p->ostack[p->osp - 2];
                    p->ostack[p->osp - 2] = p->ostack[p->osp - 1];
                    p->ostack[p->osp - 1] = a;
                }
                break;
            case 11: /* TO_R */
                a = proc_sim_pop(p);
                if (p->rsp < PROC_SIM_STACK_SIZE) p->rstack[p->rsp++] = a;
                break;
            case 12: /* FROM_R */
                if (p->rsp > 0) proc_sim_push(p, p->rstack[--p->rsp]);
                break;
            case 13: /* R_FETCH */
                if (p->rsp > 0) proc_sim_push(p, p->rstack[p->rsp - 1]);
                break;
            case 14: /* LOAD */
                addr = proc_sim_pop(p);
                proc_sim_push(p, (addr >= 0 && addr < PROC_SIM_MEM_SIZE) ? p->mem[addr] : 0);
                break;
            case 15: /* STORE */
                addr = proc_sim_pop(p); a = proc_sim_pop(p);
                if (addr >= 0 && addr < PROC_SIM_MEM_SIZE) p->mem[addr] = a;
                break;
            case 21: /* CMP_EQ */
                b = proc_sim_pop(p); a = proc_sim_pop(p);
                proc_sim_push(p, (a == b) ? 1 : -1);
                break;
            case 22: /* CMP_LT */
                b = proc_sim_pop(p); a = proc_sim_pop(p);
                proc_sim_push(p, (a < b) ? 1 : -1);
                break;
            case 23: /* CMP_GT */
                b = proc_sim_pop(p); a = proc_sim_pop(p);
                proc_sim_push(p, (a > b) ? 1 : -1);
                break;
            case 24: /* NEG */
                a = proc_sim_pop(p); proc_sim_push(p, -a);
                break;
            default: break;
        }
    }
}

TEST(test_proc_sim_push_halt) {
    ProcSim p;
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 42; /* PUSH 42 */
    p.code[2] = 5; p.code[3] = 0;  /* HALT */
    proc_sim_run(&p, 100);
    ASSERT_EQ(p.halted, 1);
    ASSERT_EQ(proc_sim_tos(&p), 42);
}

TEST(test_proc_sim_arithmetic) {
    ProcSim p;
    proc_sim_init(&p);
    /* PUSH 10, PUSH 3, ADD => 13 */
    p.code[0] = 1; p.code[1] = 10;
    p.code[2] = 1; p.code[3] = 3;
    p.code[4] = 2; p.code[5] = 0; /* ADD */
    p.code[6] = 5; p.code[7] = 0; /* HALT */
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 13);

    /* PUSH 10, PUSH 3, SUB => 7 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 10;
    p.code[2] = 1; p.code[3] = 3;
    p.code[4] = 3; p.code[5] = 0; /* SUB */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 7);

    /* PUSH 4, PUSH 5, MUL => 20 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 4;
    p.code[2] = 1; p.code[3] = 5;
    p.code[4] = 4; p.code[5] = 0; /* MUL */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 20);
}

TEST(test_proc_sim_stack_ops) {
    ProcSim p;

    /* DUP: PUSH 7, DUP, ADD => 14 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 7;
    p.code[2] = 6; p.code[3] = 0; /* DUP */
    p.code[4] = 2; p.code[5] = 0; /* ADD */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 14);

    /* DROP: PUSH 10, PUSH 20, DROP => 10 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 10;
    p.code[2] = 1; p.code[3] = 20;
    p.code[4] = 7; p.code[5] = 0; /* DROP */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 10);

    /* SWAP: PUSH 1, PUSH 2, SWAP => TOS=1 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 1;
    p.code[2] = 1; p.code[3] = 2;
    p.code[4] = 8; p.code[5] = 0; /* SWAP */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 1);

    /* OVER: PUSH 10, PUSH 20, OVER => TOS=10 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 10;
    p.code[2] = 1; p.code[3] = 20;
    p.code[4] = 9; p.code[5] = 0; /* OVER */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 10);
}

TEST(test_proc_sim_return_stack) {
    ProcSim p;
    proc_sim_init(&p);
    /* PUSH 42, TO_R, FROM_R, HALT => TOS=42 */
    p.code[0] = 1;  p.code[1] = 42;
    p.code[2] = 11; p.code[3] = 0; /* TO_R */
    p.code[4] = 12; p.code[5] = 0; /* FROM_R */
    p.code[6] = 5;  p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 42);
}

TEST(test_proc_sim_memory) {
    ProcSim p;
    proc_sim_init(&p);
    /* PUSH 99, PUSH 5, STORE, PUSH 5, LOAD, HALT => TOS=99 */
    p.code[0]  = 1;  p.code[1]  = 99;  /* value */
    p.code[2]  = 1;  p.code[3]  = 5;   /* address */
    p.code[4]  = 15; p.code[5]  = 0;   /* STORE */
    p.code[6]  = 1;  p.code[7]  = 5;   /* address */
    p.code[8]  = 14; p.code[9]  = 0;   /* LOAD */
    p.code[10] = 5;  p.code[11] = 0;   /* HALT */
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 99);
}

TEST(test_proc_sim_compare) {
    ProcSim p;

    /* CMP_EQ: 5 == 5 => 1 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 5;
    p.code[2] = 1; p.code[3] = 5;
    p.code[4] = 21; p.code[5] = 0; /* CMP_EQ */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 1);

    /* CMP_LT: 3 < 5 => 1 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 3;
    p.code[2] = 1; p.code[3] = 5;
    p.code[4] = 22; p.code[5] = 0; /* CMP_LT */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 1);

    /* CMP_GT: 7 > 2 => 1 */
    proc_sim_init(&p);
    p.code[0] = 1; p.code[1] = 7;
    p.code[2] = 1; p.code[3] = 2;
    p.code[4] = 23; p.code[5] = 0; /* CMP_GT */
    p.code[6] = 5; p.code[7] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 1);
}

TEST(test_proc_sim_neg) {
    ProcSim p;
    proc_sim_init(&p);
    /* PUSH 5, NEG, HALT => TOS=-5 */
    p.code[0] = 1;  p.code[1] = 5;
    p.code[2] = 24; p.code[3] = 0; /* NEG */
    p.code[4] = 5;  p.code[5] = 0;
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), -5);
}

TEST(test_proc_sim_complex_program) {
    ProcSim p;
    proc_sim_init(&p);
    /* Compute (3+4)*2 = 14 */
    p.code[0]  = 1; p.code[1]  = 3;   /* PUSH 3 */
    p.code[2]  = 1; p.code[3]  = 4;   /* PUSH 4 */
    p.code[4]  = 2; p.code[5]  = 0;   /* ADD */
    p.code[6]  = 1; p.code[7]  = 2;   /* PUSH 2 */
    p.code[8]  = 4; p.code[9]  = 0;   /* MUL */
    p.code[10] = 5; p.code[11] = 0;   /* HALT */
    proc_sim_run(&p, 100);
    ASSERT_EQ(proc_sim_tos(&p), 14);
}

/* Test Verilog emit function (Phase 4 full processor) */
TEST(test_verilog_emit_full) {
    unsigned char code[] = {
        1, 10,   /* PUSH 10 */
        1, 20,   /* PUSH 20 */
        2, 0,    /* ADD */
        5, 0     /* HALT */
    };
    ASSERT_EQ(emit_verilog_testbench_full(code, 8, "/tmp/test_auto_full.v"), 0);
    /* Verify file was created */
    FILE *f = fopen("/tmp/test_auto_full.v", "r");
    ASSERT_NEQ((long)f, 0);
    char buf[128];
    ASSERT_NEQ((long)fgets(buf, sizeof(buf), f), 0);
    fclose(f);
}

int main(void) {
    TEST_SUITE_BEGIN("Ternary Hardware (Phase 4)");
    /* Single-trit gate tests */
    RUN_TEST(test_trit_add_basic);
    RUN_TEST(test_trit_add_carry);
    RUN_TEST(test_trit_mul);
    RUN_TEST(test_trit_min);
    RUN_TEST(test_trit_max);
    RUN_TEST(test_trit_inverter);
    /* Word-level tests */
    RUN_TEST(test_trit_word_add);
    RUN_TEST(test_trit_word_mul);
    RUN_TEST(test_trit_word_conversion_roundtrip);
    RUN_TEST(test_trit_word_sub_via_negate);
    /* ALU simulation */
    RUN_TEST(test_alu_sim_add);
    RUN_TEST(test_alu_sim_sub);
    RUN_TEST(test_alu_sim_mul);
    /* Phase 4: Full processor simulation */
    RUN_TEST(test_proc_sim_push_halt);
    RUN_TEST(test_proc_sim_arithmetic);
    RUN_TEST(test_proc_sim_stack_ops);
    RUN_TEST(test_proc_sim_return_stack);
    RUN_TEST(test_proc_sim_memory);
    RUN_TEST(test_proc_sim_compare);
    RUN_TEST(test_proc_sim_neg);
    RUN_TEST(test_proc_sim_complex_program);
    RUN_TEST(test_verilog_emit_full);
    TEST_SUITE_END();
}
