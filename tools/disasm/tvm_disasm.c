/*
 * tvm_disasm.c — Ternary VM Bytecode Disassembler
 *
 * Part of seT6: the ternary-first microkernel OS.
 * Implements T-062 from TODOS.md.
 *
 * Features:
 *   - Labeled jump targets (auto-generated L0001 labels)
 *   - Inline trit literal display (shows -1 not 255)
 *   - Function boundary markers from ENTER/LEAVE
 *   - Annotation of CONSENSUS/ACCEPT_ANY as Kleene AND/OR
 *   - Output format: <addr>: <opcode> <operand> ; <comment>
 *
 * Build:  make tvm-disasm
 * Usage:  ./tvm_disasm <bytecode_file>
 *         ./tvm_disasm --hex <hex_string>
 *
 * Copyright 2026 seT6 contributors — MIT License
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

/* Stack effect annotations */
static const char *stack_effects[] = {
    "( -- v )",                       /* PUSH */
    "( a b -- a+b )",                 /* ADD */
    "( a b -- a*b )",                 /* MUL */
    "",                               /* JMP */
    "( c -- )",                       /* COND_JMP */
    "( v -- )",                       /* HALT */
    "( a -- v )",                     /* LOAD */
    "( a v -- )",                     /* STORE */
    "( a b -- a-b )",                 /* SUB */
    "",                               /* SYSCALL */
    "( a -- a a )",                   /* DUP */
    "( a -- )",                       /* DROP */
    "( a b -- b a )",                 /* SWAP */
    "( a b -- a b a )",               /* OVER */
    "( a b c -- b c a )",             /* ROT */
    "( v -- ) R:( -- v )",            /* TO_R */
    "R:( v -- ) ( -- v )",            /* FROM_R */
    "R:( v -- v ) ( -- v )",          /* R_FETCH */
    "",                               /* CALL */
    "",                               /* RET */
    "",                               /* ENTER */
    "",                               /* LEAVE */
    "( c -- )",                       /* BRZ */
    "( c -- )",                       /* BRN */
    "( c -- )",                       /* BRP */
    "",                               /* LOOP_BEGIN */
    "( c -- )",                       /* LOOP_END */
    "",                               /* BREAK */
    "( a b -- eq )",                  /* CMP_EQ */
    "( a b -- lt )",                  /* CMP_LT */
    "( a b -- gt )",                  /* CMP_GT */
    "( v -- -v )",                    /* NEG */
    "( a b -- min )",                 /* CONSENSUS */
    "( a b -- max )",                 /* ACCEPT_ANY */
    "( -- v )",                       /* PUSH_TRYTE */
    "( -- v )",                       /* PUSH_WORD */
    "( a b -- a/b )",                 /* DIV */
    "( a b -- a%b )",                 /* MOD */
    "( 32×trit -- lo hi )",           /* PACK64 */
    "( lo hi -- 32×trit )",           /* UNPACK64 */
    "( alo ahi blo bhi -- rlo rhi )", /* SIMD_AND */
    "( alo ahi blo bhi -- rlo rhi )", /* SIMD_OR */
    "( lo hi -- rlo rhi )",           /* SIMD_NEG */
};

/* Returns number of operand bytes for an opcode */
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

/* Is this opcode a branch/jump? */
static int is_branch(unsigned char op)
{
    return op == OP_JMP || op == OP_COND_JMP || op == OP_BRZ ||
           op == OP_BRN || op == OP_BRP || op == OP_CALL;
}

/* ── First pass: collect branch targets for labeling ── */
#define MAX_LABELS 256
static size_t labels[MAX_LABELS];
static int label_count = 0;

static int find_label(size_t addr)
{
    for (int i = 0; i < label_count; i++)
        if (labels[i] == addr)
            return i;
    return -1;
}

static int add_label(size_t addr)
{
    int idx = find_label(addr);
    if (idx >= 0)
        return idx;
    if (label_count >= MAX_LABELS)
        return -1;
    labels[label_count] = addr;
    return label_count++;
}

static void collect_labels(unsigned char *code, size_t len)
{
    size_t pc = 0;
    while (pc < len)
    {
        unsigned char op = code[pc];
        int opsz = (op < OP_COUNT) ? operand_size(op) : 0;
        if (is_branch(op) && opsz == 1 && pc + 1 < len)
        {
            add_label((size_t)(unsigned char)code[pc + 1]);
        }
        pc += 1 + (size_t)opsz;
    }
}

/* Format a trit value for display */
static const char *trit_display(int val)
{
    static char buf[16];
    if (val == -1)
        return "-1 (N)";
    else if (val == 0)
        return " 0 (Z)";
    else if (val == 1)
        return "+1 (P)";
    else
    {
        snprintf(buf, sizeof(buf), "%d", val);
        return buf;
    }
}

/* ── Syscall names ── */
static const char *syscall_name(int n)
{
    switch (n)
    {
    case 0:
        return "t_exit";
    case 1:
        return "t_write";
    case 2:
        return "t_read";
    case 3:
        return "t_mmap";
    case 4:
        return "t_cap_send";
    case 5:
        return "t_cap_recv";
    default:
        return "unknown";
    }
}

/* ── Main disassembly ── */
static void disassemble(unsigned char *code, size_t len)
{
    /* Header */
    printf("; ─── Ternary VM Disassembly ───\n");
    printf("; %zu bytes, %d label(s)\n", len, label_count);
    printf("; Opcode set: %d instructions (seT6 ISA)\n", OP_COUNT);
    printf("; Memory model: 729 cells (3^6), two-stack\n");
    printf("; ──────────────────────────────\n\n");

    int func_depth = 0;
    size_t pc = 0;

    while (pc < len)
    {
        /* Emit label if this address is a branch target */
        int lbl = find_label(pc);
        if (lbl >= 0)
            printf("L%04d:\n", lbl);

        unsigned char op = code[pc];
        const char *name = (op < OP_COUNT) ? opcode_names[op] : "???";
        int opsz = (op < OP_COUNT) ? operand_size(op) : 0;

        /* Function boundary decorations */
        if (op == OP_ENTER)
        {
            printf("; ──── function entry (depth %d) ────\n", ++func_depth);
        }

        /* Indent inside functions */
        for (int i = 0; i < func_depth; i++)
            printf("  ");

        /* Address and opcode */
        printf("  %04zu: %-12s", pc, name);

        /* Operand */
        if (opsz == 1 && pc + 1 < len)
        {
            int val = (int)(signed char)code[pc + 1];
            if (op == OP_PUSH || op == OP_PUSH_TRYTE)
            {
                /* Show trit-friendly value */
                printf(" %-6s", trit_display(val));
            }
            else if (is_branch(op))
            {
                int target = (int)(unsigned char)code[pc + 1];
                int tlbl = find_label((size_t)target);
                if (tlbl >= 0)
                    printf(" L%04d  ", tlbl);
                else
                    printf(" @%04d  ", target);
            }
            else
            {
                printf(" %d", val);
            }
        }
        else if (opsz == 2 && pc + 2 < len)
        {
            int lo = (int)(unsigned char)code[pc + 1];
            int hi = (int)(signed char)code[pc + 2];
            int val = (hi << 8) | lo;
            printf(" %d", val);
        }

        /* Comment / annotation */
        if (op < OP_COUNT && stack_effects[op][0])
            printf("  ; %s", stack_effects[op]);

        /* Special annotations */
        if (op == OP_CONSENSUS)
            printf("  — Kleene AND (trit_min)");
        if (op == OP_ACCEPT_ANY)
            printf("  — Kleene OR  (trit_max)");
        if (op == OP_NEG)
            printf("  — Ternary negation");
        if (op == OP_HALT)
            printf("  — stop execution");
        if (op == OP_SYSCALL)
        {
            /* If previous instruction was PUSH, we know the syscall number */
            if (pc >= 2 && code[pc - 2] == OP_PUSH)
                printf("  — syscall %s", syscall_name((int)(signed char)code[pc - 1]));
            else
                printf("  — dispatch to kernel");
        }
        if (op == OP_PACK64)
            printf("  — SIMD: 32 trits → packed64");
        if (op == OP_UNPACK64)
            printf("  — SIMD: packed64 → 32 trits");
        if (op == OP_SIMD_AND)
            printf("  — SIMD Kleene AND ×32");
        if (op == OP_SIMD_OR)
            printf("  — SIMD Kleene OR  ×32");
        if (op == OP_SIMD_NEG)
            printf("  — SIMD Kleene NOT ×32");

        printf("\n");

        /* Function boundary decorations */
        if (op == OP_LEAVE)
        {
            if (func_depth > 0)
                func_depth--;
            printf("; ──── function exit  (depth %d) ────\n", func_depth);
        }

        pc += 1 + (size_t)opsz;
    }

    printf("\n; ─── End (%zu bytes) ───\n", len);
}

/* ── Parse hex string to bytecode ── */
static unsigned char *parse_hex(const char *hex, size_t *out_len)
{
    size_t slen = strlen(hex);
    size_t cap = slen / 2 + 1;
    unsigned char *buf = malloc(cap);
    if (!buf)
        return NULL;
    size_t n = 0;
    for (size_t i = 0; i < slen; i += 2)
    {
        if (hex[i] == ' ' || hex[i] == ',')
        {
            i--;
            continue;
        }
        unsigned int byte;
        if (sscanf(hex + i, "%2x", &byte) != 1)
            break;
        buf[n++] = (unsigned char)byte;
    }
    *out_len = n;
    return buf;
}

/* ── Main ── */
int main(int argc, char **argv)
{
    unsigned char *bytecode = NULL;
    size_t len = 0;

    if (argc < 2)
    {
        fprintf(stderr,
                "Usage: %s <bytecode_file>\n"
                "       %s --hex \"00 03 00 05 01 05\"\n",
                argv[0], argv[0]);
        return 1;
    }

    if (strcmp(argv[1], "--hex") == 0 && argc > 2)
    {
        /* Concatenate remaining args */
        char hexbuf[4096] = {0};
        for (int i = 2; i < argc; i++)
        {
            if (i > 2)
                strcat(hexbuf, " ");
            strncat(hexbuf, argv[i], sizeof(hexbuf) - strlen(hexbuf) - 1);
        }
        bytecode = parse_hex(hexbuf, &len);
    }
    else
    {
        FILE *f = fopen(argv[1], "rb");
        if (!f)
        {
            fprintf(stderr, "Cannot open: %s\n", argv[1]);
            return 1;
        }
        fseek(f, 0, SEEK_END);
        long sz = ftell(f);
        fseek(f, 0, SEEK_SET);
        if (sz <= 0)
        {
            fclose(f);
            fprintf(stderr, "Empty file\n");
            return 1;
        }
        bytecode = malloc((size_t)sz);
        if (!bytecode)
        {
            fclose(f);
            return 1;
        }
        fread(bytecode, 1, (size_t)sz, f);
        fclose(f);
        len = (size_t)sz;
    }

    if (!bytecode || len == 0)
    {
        fprintf(stderr, "No bytecode to disassemble\n");
        return 1;
    }

    /* First pass: collect labels */
    collect_labels(bytecode, len);

    /* Second pass: disassemble */
    disassemble(bytecode, len);

    free(bytecode);
    return 0;
}
