/*
 * tvm_debug.c — Ternary VM Interactive Debugger / Stepper
 *
 * Part of seT6: the ternary-first microkernel OS.
 * Implements T-061 from TODOS.md.
 *
 * Features:
 *   step          — single-step one instruction
 *   run           — continue to HALT or breakpoint
 *   break <addr>  — set breakpoint at PC address
 *   delete <addr> — remove breakpoint
 *   breaks        — list all breakpoints
 *   stack         — print operand stack (top → bottom)
 *   rstack        — print return stack (top → bottom)
 *   mem <a> [n]   — dump n memory cells starting at address a
 *   regs          — show PC, SP, RSP, heap_top
 *   dis [s] [e]   — disassemble range [s..e) (default: around PC)
 *   reset         — reset VM state (stacks, memory, PC)
 *   load <file>   — load bytecode from file
 *   help          — show command list
 *   quit / q      — exit
 *
 * Build:  make tvm-debug
 * Usage:  ./tvm_debug [bytecode_file]
 *
 * Copyright 2026 seT6 contributors — MIT License
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* ── VM constants (mirrored from vm.h) ── */
#define STACK_SIZE 256
#define RSTACK_SIZE 256
#define MEMORY_SIZE 729 /* 3^6 */

/* ── Opcode enum (must match tools/compiler/include/vm.h) ── */
enum Opcode
{
    OP_PUSH,
    OP_ADD,
    OP_MUL,
    OP_JMP,
    OP_COND_JMP,
    OP_HALT,
    OP_LOAD,
    OP_STORE,
    OP_SUB,
    OP_SYSCALL,
    OP_DUP,
    OP_DROP,
    OP_SWAP,
    OP_OVER,
    OP_ROT,
    OP_TO_R,
    OP_FROM_R,
    OP_R_FETCH,
    OP_CALL,
    OP_RET,
    OP_ENTER,
    OP_LEAVE,
    OP_BRZ,
    OP_BRN,
    OP_BRP,
    OP_LOOP_BEGIN,
    OP_LOOP_END,
    OP_BREAK,
    OP_CMP_EQ,
    OP_CMP_LT,
    OP_CMP_GT,
    OP_NEG,
    OP_CONSENSUS,
    OP_ACCEPT_ANY,
    OP_PUSH_TRYTE,
    OP_PUSH_WORD,
    OP_DIV,
    OP_MOD,
    OP_PACK64,
    OP_UNPACK64,
    OP_SIMD_AND,
    OP_SIMD_OR,
    OP_SIMD_NEG,
    OP_COUNT
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

/* ── Returns how many operand bytes an opcode consumes ── */
static int opcode_operand_size(unsigned char op)
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

/* ── Debugger VM state (standalone, not linked to ternary_vm.c) ── */
static int ostack[STACK_SIZE]; /* operand stack */
static int sp = 0;
static int rstack[RSTACK_SIZE]; /* return stack */
static int rsp = 0;
static int memory[MEMORY_SIZE];
static int heap_top_val = MEMORY_SIZE / 2;
static unsigned char *code = NULL;
static size_t code_len = 0;
static size_t pc = 0;
static int halted = 0;
static int last_result = 0;

/* ── Breakpoints (simple array) ── */
#define MAX_BREAKPOINTS 64
static size_t breakpoints[MAX_BREAKPOINTS];
static int bp_count = 0;

/* ── Stack helpers ── */
static void push(int v)
{
    if (sp < STACK_SIZE)
        ostack[sp++] = v;
}
static int pop(void) { return sp > 0 ? ostack[--sp] : 0; }
static int peek(void) { return sp > 0 ? ostack[sp - 1] : 0; }
static void rpush(int v)
{
    if (rsp < RSTACK_SIZE)
        rstack[rsp++] = v;
}
static int rpop(void) { return rsp > 0 ? rstack[--rsp] : 0; }
static int rpeek(void) { return rsp > 0 ? rstack[rsp - 1] : 0; }

/* ── Ternary logic (simplified int-level) ── */
static int ternary_neg(int v) { return -v; }

static int ternary_consensus(int a, int b)
{
    /* Per-trit min — simplified for int values */
    return (a < b) ? a : b;
}

static int ternary_accept_any(int a, int b)
{
    return (a > b) ? a : b;
}

/* ── Check if PC is a breakpoint ── */
static int is_breakpoint(size_t addr)
{
    for (int i = 0; i < bp_count; i++)
        if (breakpoints[i] == addr)
            return 1;
    return 0;
}

/* ── Execute one instruction, advance PC. Returns 0 ok, 1 halted ── */
static int step_one(void)
{
    if (halted || pc >= code_len)
    {
        halted = 1;
        return 1;
    }

    unsigned char op = code[pc++];

    switch (op)
    {
    case OP_PUSH:
        push((int)(signed char)code[pc++]);
        break;
    case OP_ADD:
    {
        int b = pop(), a = pop();
        push(a + b);
        break;
    }
    case OP_MUL:
    {
        int b = pop(), a = pop();
        push(a * b);
        break;
    }
    case OP_SUB:
    {
        int b = pop(), a = pop();
        push(a - b);
        break;
    }
    case OP_DIV:
    {
        int b = pop(), a = pop();
        push(b ? a / b : 0);
        break;
    }
    case OP_MOD:
    {
        int b = pop(), a = pop();
        push(b ? a % b : 0);
        break;
    }
    case OP_JMP:
        pc = (size_t)code[pc];
        break;
    case OP_COND_JMP:
    {
        int c = pop();
        if (c == 0)
            pc = (size_t)code[pc];
        else
            pc++;
        break;
    }
    case OP_HALT:
        last_result = pop();
        halted = 1;
        return 1;
    case OP_LOAD:
    {
        int a = pop();
        push((a >= 0 && a < MEMORY_SIZE) ? memory[a] : 0);
        break;
    }
    case OP_STORE:
    {
        int v = pop(), a = pop();
        if (a >= 0 && a < MEMORY_SIZE)
            memory[a] = v;
        break;
    }
    case OP_SYSCALL:
    {
        int sysno = pop();
        switch (sysno)
        {
        case 0:
            halted = 1;
            return 1; /* t_exit */
        case 1:
        {
            int fd = pop(), a = pop(), s = pop();
            (void)fd;
            (void)a;
            push(s);
            break;
        }
        case 2:
        {
            int fd = pop(), a = pop(), s = pop();
            (void)fd;
            (void)a;
            (void)s;
            push(0);
            break;
        }
        case 3:
        {
            int sz = pop();
            int b = heap_top_val;
            heap_top_val += sz;
            if (heap_top_val > MEMORY_SIZE)
                heap_top_val = MEMORY_SIZE;
            push(b);
            break;
        }
        case 4:
        {
            pop();
            pop();
            push(0);
            break;
        }
        case 5:
        {
            pop();
            push(42);
            break;
        }
        default:
            push(-1);
            break;
        }
        break;
    }
    case OP_DUP:
        push(peek());
        break;
    case OP_DROP:
        pop();
        break;
    case OP_SWAP:
    {
        int b = pop(), a = pop();
        push(b);
        push(a);
        break;
    }
    case OP_OVER:
    {
        int b = pop(), a = pop();
        push(a);
        push(b);
        push(a);
        break;
    }
    case OP_ROT:
    {
        int c = pop(), b = pop(), a = pop();
        push(b);
        push(c);
        push(a);
        break;
    }
    case OP_TO_R:
        rpush(pop());
        break;
    case OP_FROM_R:
        push(rpop());
        break;
    case OP_R_FETCH:
        push(rpeek());
        break;
    case OP_CALL:
    {
        size_t t = (size_t)code[pc++];
        rpush((int)pc);
        pc = t;
        break;
    }
    case OP_RET:
        pc = (size_t)rpop();
        break;
    case OP_ENTER:
        rpush(-1);
        break;
    case OP_LEAVE:
        while (rsp > 0 && rpeek() != -1)
            rpop();
        if (rsp > 0)
            rpop();
        break;
    case OP_BRZ:
    {
        int c = pop();
        if (c == 0)
            pc = (size_t)code[pc];
        else
            pc++;
        break;
    }
    case OP_BRN:
    {
        int c = pop();
        if (c < 0)
            pc = (size_t)code[pc];
        else
            pc++;
        break;
    }
    case OP_BRP:
    {
        int c = pop();
        if (c > 0)
            pc = (size_t)code[pc];
        else
            pc++;
        break;
    }
    case OP_LOOP_BEGIN:
        rpush((int)pc);
        break;
    case OP_LOOP_END:
    {
        int c = pop();
        if (c)
            pc = (size_t)rpeek();
        else
            rpop();
        break;
    }
    case OP_BREAK:
        if (rsp > 0)
            rpop();
        while (pc < code_len && code[pc] != OP_LOOP_END)
        {
            unsigned char sk = code[pc++];
            pc += (size_t)opcode_operand_size(sk);
        }
        if (pc < code_len)
            pc++;
        break;
    case OP_CMP_EQ:
    {
        int b = pop(), a = pop();
        push(a == b ? 1 : 0);
        break;
    }
    case OP_CMP_LT:
    {
        int b = pop(), a = pop();
        push(a < b ? 1 : (a > b ? -1 : 0));
        break;
    }
    case OP_CMP_GT:
    {
        int b = pop(), a = pop();
        push(a > b ? 1 : (a < b ? -1 : 0));
        break;
    }
    case OP_NEG:
        push(ternary_neg(pop()));
        break;
    case OP_CONSENSUS:
    {
        int b = pop(), a = pop();
        push(ternary_consensus(a, b));
        break;
    }
    case OP_ACCEPT_ANY:
    {
        int b = pop(), a = pop();
        push(ternary_accept_any(a, b));
        break;
    }
    case OP_PUSH_TRYTE:
        push((int)(signed char)code[pc++]);
        break;
    case OP_PUSH_WORD:
    {
        int lo = (int)(unsigned char)code[pc++];
        int hi = (int)(signed char)code[pc++];
        push((hi << 8) | lo);
        break;
    }

    /* SIMD packed64 — simplified (pack into hi:lo int pair on stack) */
    case OP_PACK64:
    {
        unsigned long long pk = 0;
        for (int i = 31; i >= 0; i--)
        {
            int t = pop();
            unsigned enc = (t == 1) ? 1 : (t == -1) ? 2
                                                    : 0;
            pk |= ((unsigned long long)enc) << (i * 2);
        }
        push((int)(pk & 0xFFFFFFFF));
        push((int)((pk >> 32) & 0xFFFFFFFF));
        break;
    }
    case OP_UNPACK64:
    {
        unsigned long long hi = (unsigned)pop(), lo = (unsigned)pop();
        unsigned long long pk = (hi << 32) | lo;
        for (int i = 0; i < 32; i++)
        {
            unsigned enc = (pk >> (i * 2)) & 3;
            push((enc == 1) ? 1 : (enc == 2) ? -1
                                             : 0);
        }
        break;
    }
    case OP_SIMD_AND:
    case OP_SIMD_OR:
    case OP_SIMD_NEG:
    {
        /* Minimal implementation — just pop/push zeros for debugger */
        if (op == OP_SIMD_NEG)
        {
            pop();
            pop();
            push(0);
            push(0);
        }
        else
        {
            pop();
            pop();
            pop();
            pop();
            push(0);
            push(0);
        }
        break;
    }
    default:
        fprintf(stderr, "  [debug] unknown opcode %d at pc=%zu\n", op, pc - 1);
        halted = 1;
        return 1;
    }
    return 0;
}

/* ── Disassemble one instruction at addr, return next addr ── */
static size_t disasm_one(size_t addr, int show_marker)
{
    if (addr >= code_len)
    {
        printf("  (end)\n");
        return addr;
    }
    unsigned char op = code[addr];
    const char *name = (op < OP_COUNT) ? opcode_names[op] : "???";
    int opsz = (op < OP_COUNT) ? opcode_operand_size(op) : 0;

    char marker = ' ';
    if (show_marker && addr == pc)
        marker = '>';
    if (is_breakpoint(addr))
        marker = '*';
    if (show_marker && addr == pc && is_breakpoint(addr))
        marker = '#';

    printf("  %c %04zu: %-12s", marker, addr, name);
    if (opsz == 1 && addr + 1 < code_len)
    {
        int val = (int)(signed char)code[addr + 1];
        printf(" %d", val);
        /* Annotate jump targets */
        if (op == OP_JMP || op == OP_COND_JMP || op == OP_BRZ ||
            op == OP_BRN || op == OP_BRP || op == OP_CALL)
            printf("  ; → %04d", (int)(unsigned char)code[addr + 1]);
    }
    else if (opsz == 2 && addr + 2 < code_len)
    {
        int lo = (int)(unsigned char)code[addr + 1];
        int hi = (int)(signed char)code[addr + 2];
        printf(" %d", (hi << 8) | lo);
    }
    /* Annotate Kleene gates */
    if (op == OP_CONSENSUS)
        printf("  ; Kleene AND (trit_min)");
    if (op == OP_ACCEPT_ANY)
        printf("  ; Kleene OR  (trit_max)");
    if (op == OP_NEG)
        printf("  ; Kleene NOT (flip)");
    if (op == OP_ENTER)
        printf("  ; ── function entry ──");
    if (op == OP_LEAVE)
        printf("  ; ── function exit  ──");

    printf("\n");
    return addr + 1 + (size_t)opsz;
}

/* ── Reset VM ── */
static void vm_reset(void)
{
    sp = rsp = 0;
    pc = 0;
    halted = 0;
    last_result = 0;
    heap_top_val = MEMORY_SIZE / 2;
    memset(ostack, 0, sizeof(ostack));
    memset(rstack, 0, sizeof(rstack));
    memset(memory, 0, sizeof(memory));
}

/* ── Load bytecode from file ── */
static int load_bytecode(const char *path)
{
    FILE *f = fopen(path, "rb");
    if (!f)
    {
        fprintf(stderr, "  Cannot open: %s\n", path);
        return -1;
    }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz <= 0)
    {
        fclose(f);
        fprintf(stderr, "  Empty file\n");
        return -1;
    }
    unsigned char *buf = malloc((size_t)sz);
    if (!buf)
    {
        fclose(f);
        return -1;
    }
    fread(buf, 1, (size_t)sz, f);
    fclose(f);
    free(code);
    code = buf;
    code_len = (size_t)sz;
    vm_reset();
    printf("  Loaded %zu bytes from %s\n", code_len, path);
    return 0;
}

/* ── Print help ── */
static void print_help(void)
{
    printf(
        "╔═══════════════════════════════════════════════════════════╗\n"
        "║  tvm_debug — Ternary VM Debugger  (seT6 T-061)          ║\n"
        "╠═══════════════════════════════════════════════════════════╣\n"
        "║  step  [n]       Single-step n instructions (default 1)  ║\n"
        "║  run             Continue until HALT or breakpoint        ║\n"
        "║  break <addr>    Set breakpoint at PC address             ║\n"
        "║  delete <addr>   Remove breakpoint                        ║\n"
        "║  breaks          List all breakpoints                     ║\n"
        "║  stack           Show operand stack (top → bottom)        ║\n"
        "║  rstack          Show return stack  (top → bottom)        ║\n"
        "║  mem <a> [n]     Dump n memory cells from address a       ║\n"
        "║  regs            Show PC, SP, RSP, heap_top               ║\n"
        "║  dis [s] [e]     Disassemble range [s..e)                 ║\n"
        "║  reset           Reset VM state                           ║\n"
        "║  load <file>     Load bytecode from file                  ║\n"
        "║  help            Show this help                           ║\n"
        "║  quit / q        Exit debugger                            ║\n"
        "╚═══════════════════════════════════════════════════════════╝\n");
}

/* ── Trim leading/trailing whitespace ── */
static char *trim(char *s)
{
    while (*s && isspace((unsigned char)*s))
        s++;
    char *e = s + strlen(s) - 1;
    while (e > s && isspace((unsigned char)*e))
        *e-- = '\0';
    return s;
}

/* ── Main REPL ── */
int main(int argc, char **argv)
{
    printf("╔═══════════════════════════════════════════════════════════╗\n"
           "║  tvm_debug — Ternary VM Debugger  (seT6 Sigma 12)       ║\n"
           "║  43 opcodes · 2-stack · 729-cell memory · Kleene K₃     ║\n"
           "╚═══════════════════════════════════════════════════════════╝\n");

    if (argc > 1)
    {
        load_bytecode(argv[1]);
    }
    else
    {
        printf("  No bytecode file. Use 'load <file>' to load one.\n");
    }

    char line[512];
    for (;;)
    {
        /* Show PC context */
        if (code && !halted && pc < code_len)
        {
            printf("\n");
            disasm_one(pc, 1);
        }
        printf("tvm> ");
        fflush(stdout);

        if (!fgets(line, sizeof(line), stdin))
            break;
        char *cmd = trim(line);
        if (!*cmd)
            continue;

        /* ── quit ── */
        if (strcmp(cmd, "quit") == 0 || strcmp(cmd, "q") == 0)
            break;

        /* ── help ── */
        if (strcmp(cmd, "help") == 0 || strcmp(cmd, "?") == 0)
        {
            print_help();
            continue;
        }

        /* ── step [n] ── */
        if (strncmp(cmd, "step", 4) == 0 || (cmd[0] == 's' && (cmd[1] == '\0' || cmd[1] == ' ')))
        {
            int n = 1;
            char *arg = cmd + (cmd[0] == 's' && cmd[1] != 't' ? 1 : 4);
            if (*arg)
                n = atoi(arg);
            if (n < 1)
                n = 1;
            if (!code)
            {
                printf("  No bytecode loaded.\n");
                continue;
            }
            for (int i = 0; i < n; i++)
            {
                if (step_one())
                {
                    printf("  HALT (result = %d) after %d step(s)\n", last_result, i + 1);
                    break;
                }
            }
            continue;
        }

        /* ── run ── */
        if (strcmp(cmd, "run") == 0 || strcmp(cmd, "r") == 0)
        {
            if (!code)
            {
                printf("  No bytecode loaded.\n");
                continue;
            }
            int count = 0;
            while (!halted && pc < code_len)
            {
                if (count > 0 && is_breakpoint(pc))
                {
                    printf("  Breakpoint hit at %04zu after %d steps\n", pc, count);
                    break;
                }
                if (step_one())
                {
                    printf("  HALT (result = %d) after %d steps\n", last_result, count + 1);
                    break;
                }
                count++;
                if (count > 100000)
                {
                    printf("  Execution limit (100000 steps). Use 'run' again to continue.\n");
                    break;
                }
            }
            continue;
        }

        /* ── break <addr> ── */
        if (strncmp(cmd, "break ", 6) == 0)
        {
            int a = atoi(cmd + 6);
            if (a < 0)
            {
                printf("  Invalid address\n");
                continue;
            }
            if (bp_count >= MAX_BREAKPOINTS)
            {
                printf("  Max breakpoints reached\n");
                continue;
            }
            breakpoints[bp_count++] = (size_t)a;
            printf("  Breakpoint set at %04d\n", a);
            continue;
        }

        /* ── delete <addr> ── */
        if (strncmp(cmd, "delete ", 7) == 0)
        {
            size_t a = (size_t)atoi(cmd + 7);
            int found = 0;
            for (int i = 0; i < bp_count; i++)
            {
                if (breakpoints[i] == a)
                {
                    breakpoints[i] = breakpoints[--bp_count];
                    found = 1;
                    break;
                }
            }
            printf(found ? "  Breakpoint removed at %04zu\n" : "  No breakpoint at %04zu\n", a);
            continue;
        }

        /* ── breaks ── */
        if (strcmp(cmd, "breaks") == 0)
        {
            if (bp_count == 0)
            {
                printf("  No breakpoints set\n");
                continue;
            }
            printf("  Breakpoints:\n");
            for (int i = 0; i < bp_count; i++)
                printf("    [%d] %04zu\n", i, breakpoints[i]);
            continue;
        }

        /* ── stack ── */
        if (strcmp(cmd, "stack") == 0)
        {
            printf("  Operand stack (SP=%d, top first):\n", sp);
            if (sp == 0)
                printf("    (empty)\n");
            for (int i = sp - 1; i >= 0; i--)
                printf("    [%d] %d\n", i, ostack[i]);
            continue;
        }

        /* ── rstack ── */
        if (strcmp(cmd, "rstack") == 0)
        {
            printf("  Return stack (RSP=%d, top first):\n", rsp);
            if (rsp == 0)
                printf("    (empty)\n");
            for (int i = rsp - 1; i >= 0; i--)
                printf("    [%d] %d\n", i, rstack[i]);
            continue;
        }

        /* ── mem <addr> [count] ── */
        if (strncmp(cmd, "mem ", 4) == 0)
        {
            int a = 0, n = 16;
            sscanf(cmd + 4, "%d %d", &a, &n);
            if (a < 0)
                a = 0;
            if (n < 1)
                n = 1;
            if (n > 256)
                n = 256;
            printf("  Memory [%d..%d):\n", a, a + n);
            for (int i = 0; i < n && (a + i) < MEMORY_SIZE; i++)
            {
                if (i % 9 == 0)
                    printf("    %04d:", a + i);
                printf(" %3d", memory[a + i]);
                if (i % 9 == 8 || i == n - 1)
                    printf("\n");
            }
            continue;
        }

        /* ── regs ── */
        if (strcmp(cmd, "regs") == 0)
        {
            printf("  PC=%04zu  SP=%d  RSP=%d  heap=%d  halted=%d  result=%d\n",
                   pc, sp, rsp, heap_top_val, halted, last_result);
            if (sp > 0)
                printf("  TOS=%d\n", ostack[sp - 1]);
            continue;
        }

        /* ── dis [start] [end] ── */
        if (strncmp(cmd, "dis", 3) == 0)
        {
            if (!code)
            {
                printf("  No bytecode loaded.\n");
                continue;
            }
            size_t s = 0, e = code_len;
            if (strlen(cmd) > 3)
            {
                int si = 0, ei = (int)code_len;
                sscanf(cmd + 3, "%d %d", &si, &ei);
                s = (size_t)(si < 0 ? 0 : si);
                e = (size_t)((size_t)ei > code_len ? (int)code_len : ei);
            }
            else
            {
                /* Default: 5 before PC to 10 after */
                s = pc >= 5 ? pc - 5 : 0;
                e = pc + 20;
                if (e > code_len)
                    e = code_len;
            }
            printf("  Disassembly [%04zu..%04zu):\n", s, e);
            size_t a = s;
            while (a < e)
                a = disasm_one(a, 1);
            continue;
        }

        /* ── reset ── */
        if (strcmp(cmd, "reset") == 0)
        {
            vm_reset();
            printf("  VM reset. PC=0, stacks cleared, memory zeroed.\n");
            continue;
        }

        /* ── load <file> ── */
        if (strncmp(cmd, "load ", 5) == 0)
        {
            load_bytecode(cmd + 5);
            continue;
        }

        printf("  Unknown command: '%s'. Type 'help' for commands.\n", cmd);
    }

    free(code);
    printf("Goodbye.\n");
    return 0;
}
