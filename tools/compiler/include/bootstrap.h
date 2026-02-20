/*
 * bootstrap.h - Self-Hosting Bootstrap Interface (TASK-018)
 *
 * Defines the interface for a minimal self-hosting compiler.
 * The bootstrap compiler can compile a subset of C (the "seT5-C" subset)
 * that is sufficient to express the tokenizer itself.
 *
 * seT5-C Subset:
 *   - int variables and pointers (int, int *)
 *   - Arithmetic: +, -, *, =
 *   - Control: if/else, while, return
 *   - Functions with int params and return
 *   - Character literals ('a')
 *   - Array indexing: a[i]
 *   - String constants (for error messages)
 *
 * The bootstrap pipeline:
 *   1. Parse seT5-C source -> AST
 *   2. Constant fold (optimize pass)
 *   3. Emit ternary bytecode
 *   4. The emitted bytecode can tokenize C source
 */

#ifndef BOOTSTRAP_H
#define BOOTSTRAP_H

#include "ir.h"
#include "parser.h"
#include "codegen.h"
#include "vm.h"

/* Maximum source size for bootstrap compilation */
#define BOOTSTRAP_MAX_SRC 4096

/* Symbol table entry for the bootstrap compiler */
typedef struct {
    char name[64];
    int stack_offset;  /* Offset from frame pointer in stack slots */
    int is_pointer;    /* 1 if the var is a pointer type */
} BootstrapSymbol;

#define MAX_SYMBOLS 64

typedef struct {
    BootstrapSymbol symbols[MAX_SYMBOLS];
    int count;
    int next_offset;
} BootstrapSymTab;

/* Initialize a symbol table */
static inline void symtab_init(BootstrapSymTab *tab) {
    tab->count = 0;
    tab->next_offset = 0;
}

/* Add a symbol, return its stack offset */
static inline int symtab_add(BootstrapSymTab *tab, const char *name, int is_ptr) {
    if (tab->count >= MAX_SYMBOLS) return -1;
    BootstrapSymbol *s = &tab->symbols[tab->count++];
    strncpy(s->name, name, 63);
    s->name[63] = '\0';
    s->is_pointer = is_ptr;
    s->stack_offset = tab->next_offset++;
    return s->stack_offset;
}

/* Lookup a symbol, return stack offset or -1 if not found */
static inline int symtab_lookup(BootstrapSymTab *tab, const char *name) {
    for (int i = 0; i < tab->count; i++) {
        if (strcmp(tab->symbols[i].name, name) == 0)
            return tab->symbols[i].stack_offset;
    }
    return -1;
}

/*
 * bootstrap_compile: Compile a seT5-C source string to bytecode.
 * Returns the bytecode length, or -1 on error.
 *
 * The compilation uses the existing parser + IR + codegen pipeline:
 *   1. parse_program(source) -> AST
 *   2. optimize(AST) -> folded AST
 *   3. Emit bytecode from AST (using symbol table for var offsets)
 */
int bootstrap_compile(const char *source, unsigned char *out_bytecode, int max_len);

/*
 * bootstrap_self_test: Compiles the mini-tokenizer source and runs it.
 * Returns 0 on success, 1 on failure.
 */
int bootstrap_self_test(void);

#endif /* BOOTSTRAP_H */
