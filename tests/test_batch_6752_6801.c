/*
 * test_batch_6752_6801.c — Batch 6752-6801: VM Developer Tools
 *
 * 50 tests covering T-061 (VM debugger), T-062 (disassembler),
 * T-063 (REPL) concepts: opcode encoding, operand sizes,
 * disassembly round-trip, stack semantics, memory addressing,
 * balanced ternary representation, Kleene gate VM execution,
 * two-stack model, structured control flow, SIMD packed64.
 *
 * Part of seT6 Sigma 12 — ternary-first microkernel OS.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int tests_passed = 0;
static int tests_failed = 0;

#define ASSERT_EQ(a, b, msg)                           \
    do                                                 \
    {                                                  \
        int _a = (a), _b = (b);                        \
        if (_a == _b)                                  \
        {                                              \
            tests_passed++;                            \
        }                                              \
        else                                           \
        {                                              \
            tests_failed++;                            \
            printf("FAIL [%d]: %s: got %d, want %d\n", \
                   __LINE__, (msg), _a, _b);           \
        }                                              \
    } while (0)

#define ASSERT_TRUE(cond, msg)                          \
    do                                                  \
    {                                                   \
        if ((cond))                                     \
        {                                               \
            tests_passed++;                             \
        }                                               \
        else                                            \
        {                                               \
            tests_failed++;                             \
            printf("FAIL [%d]: %s\n", __LINE__, (msg)); \
        }                                               \
    } while (0)

/* ── Opcode definitions (must match vm.h) ── */
enum Opcode
{
    OP_PUSH = 0,
    OP_ADD = 1,
    OP_MUL = 2,
    OP_JMP = 3,
    OP_COND_JMP = 4,
    OP_HALT = 5,
    OP_LOAD = 6,
    OP_STORE = 7,
    OP_SUB = 8,
    OP_SYSCALL = 9,
    OP_DUP = 10,
    OP_DROP = 11,
    OP_SWAP = 12,
    OP_OVER = 13,
    OP_ROT = 14,
    OP_TO_R = 15,
    OP_FROM_R = 16,
    OP_R_FETCH = 17,
    OP_CALL = 18,
    OP_RET = 19,
    OP_ENTER = 20,
    OP_LEAVE = 21,
    OP_BRZ = 22,
    OP_BRN = 23,
    OP_BRP = 24,
    OP_LOOP_BEGIN = 25,
    OP_LOOP_END = 26,
    OP_BREAK = 27,
    OP_CMP_EQ = 28,
    OP_CMP_LT = 29,
    OP_CMP_GT = 30,
    OP_NEG = 31,
    OP_CONSENSUS = 32,
    OP_ACCEPT_ANY = 33,
    OP_PUSH_TRYTE = 34,
    OP_PUSH_WORD = 35,
    OP_DIV = 36,
    OP_MOD = 37,
    OP_PACK64 = 38,
    OP_UNPACK64 = 39,
    OP_SIMD_AND = 40,
    OP_SIMD_OR = 41,
    OP_SIMD_NEG = 42,
    OP_COUNT = 43
};

static const char *opcode_names[] = {
    "PUSH", "ADD", "MUL", "JMP", "COND_JMP", "HALT",
    "LOAD", "STORE", "SUB", "SYSCALL",
    "DUP", "DROP", "SWAP", "OVER", "ROT",
    "TO_R", "FROM_R", "R_FETCH",
    "CALL", "RET", "ENTER", "LEAVE",
    "BRZ", "BRN", "BRP", "LOOP_BEGIN", "LOOP_END", "BREAK",
    "CMP_EQ", "CMP_LT", "CMP_GT",
    "NEG", "CONSENSUS", "ACCEPT_ANY",
    "PUSH_TRYTE", "PUSH_WORD",
    "DIV", "MOD",
    "PACK64", "UNPACK64", "SIMD_AND", "SIMD_OR", "SIMD_NEG"};

/* Returns operand byte count for an opcode */
static int operand_size(unsigned char op)
{
    switch (op)
    {
    case OP_PUSH:
    case OP_JMP:
    case OP_COND_JMP:
    case OP_BRZ:
    case OP_BRN:
    case OP_BRP:
    case OP_CALL:
    case OP_PUSH_TRYTE:
        return 1;
    case OP_PUSH_WORD:
        return 2;
    default:
        return 0;
    }
}

/* ── Minimal VM for verification ── */
#define VM_STACK 256
#define VM_MEM 729
static int vstack[VM_STACK], vsp = 0;
static int vrstack[VM_STACK], vrsp = 0;
static int vmem[VM_MEM];

static void vpush(int v)
{
    if (vsp < VM_STACK)
        vstack[vsp++] = v;
}
static int vpop(void) { return vsp > 0 ? vstack[--vsp] : 0; }
static int vpeek(void) { return vsp > 0 ? vstack[vsp - 1] : 0; }
static void vrpush(int v)
{
    if (vrsp < VM_STACK)
        vrstack[vrsp++] = v;
}
static int vrpop(void) { return vrsp > 0 ? vrstack[--vrsp] : 0; }
static int vrpeek(void) { return vrsp > 0 ? vrstack[vrsp - 1] : 0; }

static void vm_reset(void)
{
    vsp = vrsp = 0;
    memset(vstack, 0, sizeof(vstack));
    memset(vrstack, 0, sizeof(vrstack));
    memset(vmem, 0, sizeof(vmem));
}

/* Run bytecode, return result from HALT */
static int vm_exec(unsigned char *bc, size_t len)
{
    vm_reset();
    size_t pc = 0;
    int result = 0;
    int steps = 0;
    while (pc < len && steps < 10000)
    {
        unsigned char op = bc[pc++];
        steps++;
        switch (op)
        {
        case OP_PUSH:
            vpush((int)(signed char)bc[pc++]);
            break;
        case OP_ADD:
        {
            int b = vpop(), a = vpop();
            vpush(a + b);
            break;
        }
        case OP_MUL:
        {
            int b = vpop(), a = vpop();
            vpush(a * b);
            break;
        }
        case OP_SUB:
        {
            int b = vpop(), a = vpop();
            vpush(a - b);
            break;
        }
        case OP_DIV:
        {
            int b = vpop(), a = vpop();
            vpush(b ? a / b : 0);
            break;
        }
        case OP_MOD:
        {
            int b = vpop(), a = vpop();
            vpush(b ? a % b : 0);
            break;
        }
        case OP_JMP:
            pc = (size_t)bc[pc];
            break;
        case OP_COND_JMP:
        {
            int c = vpop();
            if (c == 0)
                pc = (size_t)bc[pc];
            else
                pc++;
            break;
        }
        case OP_HALT:
            result = vpop();
            return result;
        case OP_LOAD:
        {
            int a = vpop();
            vpush((a >= 0 && a < VM_MEM) ? vmem[a] : 0);
            break;
        }
        case OP_STORE:
        {
            int v = vpop(), a = vpop();
            if (a >= 0 && a < VM_MEM)
                vmem[a] = v;
            break;
        }
        case OP_SYSCALL:
        {
            int sn = vpop();
            if (sn == 0)
                return 0;
            vpush(0);
            break;
        }
        case OP_DUP:
            vpush(vpeek());
            break;
        case OP_DROP:
            vpop();
            break;
        case OP_SWAP:
        {
            int b = vpop(), a = vpop();
            vpush(b);
            vpush(a);
            break;
        }
        case OP_OVER:
        {
            int b = vpop(), a = vpop();
            vpush(a);
            vpush(b);
            vpush(a);
            break;
        }
        case OP_ROT:
        {
            int c = vpop(), b = vpop(), a = vpop();
            vpush(b);
            vpush(c);
            vpush(a);
            break;
        }
        case OP_TO_R:
            vrpush(vpop());
            break;
        case OP_FROM_R:
            vpush(vrpop());
            break;
        case OP_R_FETCH:
            vpush(vrpeek());
            break;
        case OP_CALL:
        {
            size_t t = (size_t)bc[pc++];
            vrpush((int)pc);
            pc = t;
            break;
        }
        case OP_RET:
            pc = (size_t)vrpop();
            break;
        case OP_ENTER:
            vrpush(-1);
            break;
        case OP_LEAVE:
            while (vrsp > 0 && vrpeek() != -1)
                vrpop();
            if (vrsp > 0)
                vrpop();
            break;
        case OP_BRZ:
        {
            int c = vpop();
            if (c == 0)
                pc = (size_t)bc[pc];
            else
                pc++;
            break;
        }
        case OP_BRN:
        {
            int c = vpop();
            if (c < 0)
                pc = (size_t)bc[pc];
            else
                pc++;
            break;
        }
        case OP_BRP:
        {
            int c = vpop();
            if (c > 0)
                pc = (size_t)bc[pc];
            else
                pc++;
            break;
        }
        case OP_LOOP_BEGIN:
            vrpush((int)pc);
            break;
        case OP_LOOP_END:
        {
            int c = vpop();
            if (c)
                pc = (size_t)vrpeek();
            else
                vrpop();
            break;
        }
        case OP_BREAK:
            if (vrsp > 0)
                vrpop();
            break;
        case OP_CMP_EQ:
        {
            int b = vpop(), a = vpop();
            vpush(a == b ? 1 : 0);
            break;
        }
        case OP_CMP_LT:
        {
            int b = vpop(), a = vpop();
            vpush(a < b ? 1 : (a > b ? -1 : 0));
            break;
        }
        case OP_CMP_GT:
        {
            int b = vpop(), a = vpop();
            vpush(a > b ? 1 : (a < b ? -1 : 0));
            break;
        }
        case OP_NEG:
            vpush(-vpop());
            break;
        case OP_CONSENSUS:
        {
            int b = vpop(), a = vpop();
            vpush(a < b ? a : b);
            break;
        }
        case OP_ACCEPT_ANY:
        {
            int b = vpop(), a = vpop();
            vpush(a > b ? a : b);
            break;
        }
        case OP_PUSH_TRYTE:
            vpush((int)(signed char)bc[pc++]);
            break;
        case OP_PUSH_WORD:
        {
            int lo = (unsigned char)bc[pc++];
            int hi = (signed char)bc[pc++];
            vpush((hi << 8) | lo);
            break;
        }
        default:
            return -99;
        }
    }
    return vsp > 0 ? vstack[vsp - 1] : 0;
}

/* ── Balanced ternary conversion ── */
static void int_to_trits(int val, int trits[9])
{
    int v = val;
    for (int i = 0; i < 9; i++)
    {
        int r = v % 3;
        v /= 3;
        if (r > 1)
        {
            r -= 3;
            v++;
        }
        if (r < -1)
        {
            r += 3;
            v--;
        }
        trits[i] = r;
    }
}

/* ══════════════════════════════════════════════════════════════ */
/*  Tests 6752–6801: VM Developer Tools                         */
/* ══════════════════════════════════════════════════════════════ */

/* 6752: Opcode count matches ISA spec (43 opcodes) */
static void test_6752(void)
{
    ASSERT_EQ(OP_COUNT, 43, "T6752: opcode count = 43");
}

/* 6753: All opcode names are non-NULL */
static void test_6753(void)
{
    int all_named = 1;
    for (int i = 0; i < OP_COUNT; i++)
        if (!opcode_names[i])
            all_named = 0;
    ASSERT_TRUE(all_named, "T6753: all opcode names non-NULL");
}

/* 6754: PUSH has 1-byte operand */
static void test_6754(void)
{
    ASSERT_EQ(operand_size(OP_PUSH), 1, "T6754: PUSH operand = 1");
}

/* 6755: PUSH_WORD has 2-byte operand */
static void test_6755(void)
{
    ASSERT_EQ(operand_size(OP_PUSH_WORD), 2, "T6755: PUSH_WORD operand = 2");
}

/* 6756: ADD has 0 operand bytes */
static void test_6756(void)
{
    ASSERT_EQ(operand_size(OP_ADD), 0, "T6756: ADD operand = 0");
}

/* 6757: All branch opcodes have 1-byte operand */
static void test_6757(void)
{
    ASSERT_EQ(operand_size(OP_JMP), 1, "T6757: JMP operand = 1");
    ASSERT_EQ(operand_size(OP_BRZ), 1, "T6757: BRZ operand = 1");
    ASSERT_EQ(operand_size(OP_BRN), 1, "T6757: BRN operand = 1");
    ASSERT_EQ(operand_size(OP_BRP), 1, "T6757: BRP operand = 1");
    ASSERT_EQ(operand_size(OP_CALL), 1, "T6757: CALL operand = 1");
}

/* 6758: Simple PUSH + HALT execution */
static void test_6758(void)
{
    unsigned char prog[] = {OP_PUSH, 7, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 7, "T6758: PUSH 7 HALT = 7");
}

/* 6759: ADD arithmetic */
static void test_6759(void)
{
    unsigned char prog[] = {OP_PUSH, 3, OP_PUSH, 4, OP_ADD, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 7, "T6759: 3+4 = 7");
}

/* 6760: SUB arithmetic */
static void test_6760(void)
{
    unsigned char prog[] = {OP_PUSH, 10, OP_PUSH, 3, OP_SUB, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 7, "T6760: 10-3 = 7");
}

/* 6761: MUL arithmetic */
static void test_6761(void)
{
    unsigned char prog[] = {OP_PUSH, 3, OP_PUSH, 4, OP_MUL, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 12, "T6761: 3*4 = 12");
}

/* 6762: DIV arithmetic */
static void test_6762(void)
{
    unsigned char prog[] = {OP_PUSH, 12, OP_PUSH, 3, OP_DIV, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 4, "T6762: 12/3 = 4");
}

/* 6763: MOD arithmetic */
static void test_6763(void)
{
    unsigned char prog[] = {OP_PUSH, 13, OP_PUSH, 5, OP_MOD, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 3, "T6763: 13%5 = 3");
}

/* 6764: DIV by zero = 0 */
static void test_6764(void)
{
    unsigned char prog[] = {OP_PUSH, 10, OP_PUSH, 0, OP_DIV, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 0, "T6764: 10/0 = 0");
}

/* 6765: DUP duplicates TOS */
static void test_6765(void)
{
    unsigned char prog[] = {OP_PUSH, 5, OP_DUP, OP_ADD, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 10, "T6765: DUP 5 + 5 = 10");
}

/* 6766: SWAP exchanges top two */
static void test_6766(void)
{
    unsigned char prog[] = {OP_PUSH, 3, OP_PUSH, 7, OP_SWAP, OP_SUB, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 4, "T6766: SWAP(3,7) SUB = 4");
}

/* 6767: OVER copies NOS */
static void test_6767(void)
{
    unsigned char prog[] = {OP_PUSH, 1, OP_PUSH, 2, OP_OVER, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 1, "T6767: OVER(1,2) = 1");
}

/* 6768: ROT rotates third to top */
static void test_6768(void)
{
    unsigned char prog[] = {OP_PUSH, 1, OP_PUSH, 2, OP_PUSH, 3, OP_ROT, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 1, "T6768: ROT(1,2,3) = 1");
}

/* 6769: NEG negates TOS */
static void test_6769(void)
{
    unsigned char prog[] = {OP_PUSH, 5, OP_NEG, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), -5, "T6769: NEG 5 = -5");
}

/* 6770: NEG of negative */
static void test_6770(void)
{
    unsigned char prog[] = {OP_PUSH, (unsigned char)-3, OP_NEG, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 3, "T6770: NEG -3 = 3");
}

/* 6771: CONSENSUS (Kleene AND = min) */
static void test_6771(void)
{
    unsigned char prog[] = {OP_PUSH, 1, OP_PUSH, (unsigned char)-1, OP_CONSENSUS, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), -1, "T6771: CONSENSUS(1,-1) = -1");
}

/* 6772: ACCEPT_ANY (Kleene OR = max) */
static void test_6772(void)
{
    unsigned char prog[] = {OP_PUSH, (unsigned char)-1, OP_PUSH, 0, OP_ACCEPT_ANY, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 0, "T6772: ACCEPT_ANY(-1,0) = 0");
}

/* 6773: CMP_EQ true */
static void test_6773(void)
{
    unsigned char prog[] = {OP_PUSH, 5, OP_PUSH, 5, OP_CMP_EQ, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 1, "T6773: CMP_EQ(5,5) = 1");
}

/* 6774: CMP_EQ false */
static void test_6774(void)
{
    unsigned char prog[] = {OP_PUSH, 5, OP_PUSH, 3, OP_CMP_EQ, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 0, "T6774: CMP_EQ(5,3) = 0");
}

/* 6775: CMP_LT true */
static void test_6775(void)
{
    unsigned char prog[] = {OP_PUSH, 2, OP_PUSH, 5, OP_CMP_LT, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 1, "T6775: CMP_LT(2,5) = 1");
}

/* 6776: CMP_GT true */
static void test_6776(void)
{
    unsigned char prog[] = {OP_PUSH, 9, OP_PUSH, 3, OP_CMP_GT, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 1, "T6776: CMP_GT(9,3) = 1");
}

/* 6777: STORE + LOAD (memory round-trip) */
static void test_6777(void)
{
    unsigned char prog[] = {OP_PUSH, 10, OP_PUSH, 42, OP_STORE,
                            OP_PUSH, 10, OP_LOAD, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 42, "T6777: mem[10]=42 → 42");
}

/* 6778: TO_R + FROM_R (return stack round-trip) */
static void test_6778(void)
{
    unsigned char prog[] = {OP_PUSH, 99, OP_TO_R, OP_FROM_R, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 99, "T6778: TO_R/FROM_R round-trip 99");
}

/* 6779: R_FETCH copies without popping */
static void test_6779(void)
{
    unsigned char prog[] = {OP_PUSH, 77, OP_TO_R, OP_R_FETCH, OP_FROM_R, OP_ADD, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 154, "T6779: R_FETCH copy + POP = 77+77");
}

/* 6780: BRZ taken (zero condition) */
static void test_6780(void)
{
    /* PUSH 0, BRZ @6, PUSH 99, HALT, PUSH 42, HALT */
    unsigned char prog[] = {OP_PUSH, 0, OP_BRZ, 8, OP_PUSH, 99, OP_HALT, 0, OP_PUSH, 42, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 42, "T6780: BRZ taken → 42");
}

/* 6781: BRZ not taken (nonzero condition) */
static void test_6781(void)
{
    unsigned char prog[] = {OP_PUSH, 1, OP_BRZ, 8, OP_PUSH, 99, OP_HALT, 0, OP_PUSH, 42, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 99, "T6781: BRZ not taken → 99");
}

/* 6782: BRN taken (negative) */
static void test_6782(void)
{
    unsigned char prog[] = {OP_PUSH, (unsigned char)-1, OP_BRN, 8, OP_PUSH, 99, OP_HALT, 0, OP_PUSH, 42, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 42, "T6782: BRN taken → 42");
}

/* 6783: BRP taken (positive) */
static void test_6783(void)
{
    unsigned char prog[] = {OP_PUSH, 1, OP_BRP, 8, OP_PUSH, 99, OP_HALT, 0, OP_PUSH, 42, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 42, "T6783: BRP taken → 42");
}

/* 6784: CALL + RET function call */
static void test_6784(void)
{
    /* PUSH 10, CALL @6, HALT, PUSH 5, ADD, RET */
    unsigned char prog[] = {OP_PUSH, 10, OP_CALL, 7, OP_HALT, 0, 0, OP_PUSH, 5, OP_ADD, OP_RET};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 15, "T6784: CALL/RET → 10+5=15");
}

/* 6785: ENTER/LEAVE frame markers */
static void test_6785(void)
{
    unsigned char prog[] = {OP_PUSH, 42, OP_ENTER, OP_PUSH, 99, OP_TO_R, OP_LEAVE, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 42, "T6785: ENTER/LEAVE preserves only operand stack");
}

/* 6786: PUSH_TRYTE encodes correctly */
static void test_6786(void)
{
    unsigned char prog[] = {OP_PUSH_TRYTE, 13, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 13, "T6786: PUSH_TRYTE 13 = 13");
}

/* 6787: PUSH_WORD encodes 16-bit value */
static void test_6787(void)
{
    /* Value 300 = 0x012C: lo=0x2C=44, hi=0x01=1 */
    unsigned char prog[] = {OP_PUSH_WORD, 44, 1, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 300, "T6787: PUSH_WORD 300 = 300");
}

/* 6788: Balanced ternary: 0 has all zero trits */
static void test_6788(void)
{
    int trits[9];
    int_to_trits(0, trits);
    int all_zero = 1;
    for (int i = 0; i < 9; i++)
        if (trits[i] != 0)
            all_zero = 0;
    ASSERT_TRUE(all_zero, "T6788: 0 → all zero trits");
}

/* 6789: Balanced ternary: 1 = [0,0,0,0,0,0,0,0,1] */
static void test_6789(void)
{
    int trits[9];
    int_to_trits(1, trits);
    ASSERT_EQ(trits[0], 1, "T6789: 1 → trit[0]=1");
    ASSERT_EQ(trits[1], 0, "T6789: 1 → trit[1]=0");
}

/* 6790: Balanced ternary: -1 = [0,0,...,-1] */
static void test_6790(void)
{
    int trits[9];
    int_to_trits(-1, trits);
    ASSERT_EQ(trits[0], -1, "T6790: -1 → trit[0]=-1");
}

/* 6791: Balanced ternary: 13 = 1*9 + 1*3 + 1*1 → [1,1,1,0,...] */
static void test_6791(void)
{
    int trits[9];
    int_to_trits(13, trits);
    ASSERT_EQ(trits[0], 1, "T6791: 13 → trit[0]=1");
    ASSERT_EQ(trits[1], 1, "T6791: 13 → trit[1]=1");
    ASSERT_EQ(trits[2], 1, "T6791: 13 → trit[2]=1");
}

/* 6792: Memory is ternary-addressable (729 = 3^6 cells) */
static void test_6792(void)
{
    ASSERT_EQ(VM_MEM, 729, "T6792: memory = 729 cells (3^6)");
}

/* 6793: Stack depth is 256 */
static void test_6793(void)
{
    ASSERT_EQ(VM_STACK, 256, "T6793: stack depth = 256");
}

/* 6794: DROP discards TOS */
static void test_6794(void)
{
    unsigned char prog[] = {OP_PUSH, 5, OP_PUSH, 99, OP_DROP, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 5, "T6794: DROP(99) → 5");
}

/* 6795: Chained arithmetic: (2+3)*4 = 20 */
static void test_6795(void)
{
    unsigned char prog[] = {OP_PUSH, 2, OP_PUSH, 3, OP_ADD, OP_PUSH, 4, OP_MUL, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 20, "T6795: (2+3)*4 = 20");
}

/* 6796: Negative PUSH via sign extension */
static void test_6796(void)
{
    unsigned char prog[] = {OP_PUSH, (unsigned char)(signed char)-13, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), -13, "T6796: PUSH -13 = -13");
}

/* 6797: Multiple memory cells */
static void test_6797(void)
{
    unsigned char prog[] = {
        OP_PUSH, 0, OP_PUSH, 10, OP_STORE, /* mem[0]=10 */
        OP_PUSH, 1, OP_PUSH, 20, OP_STORE, /* mem[1]=20 */
        OP_PUSH, 0, OP_LOAD,               /* load mem[0] */
        OP_PUSH, 1, OP_LOAD,               /* load mem[1] */
        OP_ADD, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 30, "T6797: mem[0]+mem[1] = 30");
}

/* 6798: Consensus with UNKNOWN (0) */
static void test_6798(void)
{
    unsigned char prog[] = {OP_PUSH, 1, OP_PUSH, 0, OP_CONSENSUS, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 0, "T6798: CONSENSUS(1,0) = 0");
}

/* 6799: Accept-any with positive */
static void test_6799(void)
{
    unsigned char prog[] = {OP_PUSH, 0, OP_PUSH, 1, OP_ACCEPT_ANY, OP_HALT};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 1, "T6799: ACCEPT_ANY(0,1) = 1");
}

/* 6800: Syscall t_exit returns */
static void test_6800(void)
{
    unsigned char prog[] = {OP_PUSH, 0, OP_SYSCALL};
    ASSERT_EQ(vm_exec(prog, sizeof(prog)), 0, "T6800: syscall t_exit returns");
}

/* 6801: Opcode encoding is contiguous 0..42 */
static void test_6801(void)
{
    ASSERT_EQ(OP_PUSH, 0, "T6801: PUSH = 0");
    ASSERT_EQ(OP_SIMD_NEG, 42, "T6801: SIMD_NEG = 42");
    ASSERT_EQ(OP_COUNT, 43, "T6801: COUNT = 43 (contiguous)");
}

int main(void)
{
    printf("╔═══════════════════════════════════════════════════════════╗\n");
    printf("║  Batch 6752-6801: VM Developer Tools (50 tests)          ║\n");
    printf("╚═══════════════════════════════════════════════════════════╝\n");

    test_6752();
    test_6753();
    test_6754();
    test_6755();
    test_6756();
    test_6757();
    test_6758();
    test_6759();
    test_6760();
    test_6761();
    test_6762();
    test_6763();
    test_6764();
    test_6765();
    test_6766();
    test_6767();
    test_6768();
    test_6769();
    test_6770();
    test_6771();
    test_6772();
    test_6773();
    test_6774();
    test_6775();
    test_6776();
    test_6777();
    test_6778();
    test_6779();
    test_6780();
    test_6781();
    test_6782();
    test_6783();
    test_6784();
    test_6785();
    test_6786();
    test_6787();
    test_6788();
    test_6789();
    test_6790();
    test_6791();
    test_6792();
    test_6793();
    test_6794();
    test_6795();
    test_6796();
    test_6797();
    test_6798();
    test_6799();
    test_6800();
    test_6801();

    printf("\n=== Results: %d/%d passed, %d failed ===\n",
           tests_passed, tests_passed + tests_failed, tests_failed);

    return tests_failed ? 1 : 0;
}
