/*
 * linker.h - Ternary Bytecode Linker (Phase 3)
 *
 * Resolves symbols across multiple compilation units.
 * Links function calls to their bytecode addresses and
 * merges separate object modules into a single executable.
 *
 * Object module format:
 *   - Header: symbol table (exports + imports)
 *   - Body: bytecode with relocation entries
 *
 * The linker performs:
 *   1. Symbol collection from all modules
 *   2. Duplicate/missing symbol detection
 *   3. Address relocation (patching CALL targets)
 *   4. Final executable assembly
 */

#ifndef LINKER_H
#define LINKER_H

#include <stddef.h>

/* Maximum limits */
#define LINK_MAX_SYMBOLS   128
#define LINK_MAX_MODULES   16
#define LINK_MAX_RELOCS    256
#define LINK_MAX_CODE      4096

/* Symbol visibility */
typedef enum {
    SYM_EXPORT,   /* Defined in this module, visible to others */
    SYM_IMPORT,   /* Used in this module, defined elsewhere */
    SYM_LOCAL     /* Internal to this module */
} SymVisibility;

/* Linker symbol */
typedef struct {
    char name[64];
    int address;          /* Bytecode address (absolute after linking) */
    int module_id;        /* Which module defines this symbol */
    SymVisibility vis;
} LinkSymbol;

/* Relocation entry: a place in bytecode that needs patching */
typedef struct {
    int offset;           /* Byte offset in the module's bytecode */
    char target_name[64]; /* Symbol name to resolve */
    int module_id;        /* Module containing this relocation */
} Relocation;

/* Object module */
typedef struct {
    int id;
    unsigned char code[LINK_MAX_CODE];
    int code_len;
    LinkSymbol symbols[LINK_MAX_SYMBOLS];
    int sym_count;
    Relocation relocs[LINK_MAX_RELOCS];
    int reloc_count;
    int base_addr;        /* Base address after linking */
} ObjectModule;

/* Linker state */
typedef struct {
    ObjectModule modules[LINK_MAX_MODULES];
    int module_count;

    /* Global symbol table (merged) */
    LinkSymbol globals[LINK_MAX_SYMBOLS];
    int global_count;

    /* Output executable */
    unsigned char output[LINK_MAX_CODE];
    int output_len;

    /* Error tracking */
    char errors[16][128];
    int error_count;
} Linker;

/* Initialize the linker */
void linker_init(Linker *lnk);

/* Add an object module. Returns the module ID or -1 on error. */
int linker_add_module(Linker *lnk, const unsigned char *code, int code_len);

/* Add a symbol to a module */
int linker_add_symbol(Linker *lnk, int module_id, const char *name,
                      int address, SymVisibility vis);

/* Add a relocation to a module */
int linker_add_reloc(Linker *lnk, int module_id, int offset,
                     const char *target_name);

/* Link all modules. Returns 0 on success, error count on failure.
 * On success, output is in lnk->output[0..lnk->output_len-1]. */
int linker_link(Linker *lnk);

/* Resolve a single symbol by name. Returns address or -1 if not found. */
int linker_resolve(const Linker *lnk, const char *name);

/* Report linker errors to stderr */
void linker_report_errors(const Linker *lnk);

#endif /* LINKER_H */
