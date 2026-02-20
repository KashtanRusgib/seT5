/*
 * typechecker.h - Type Checking for Ternary Compiler (Phase 3)
 *
 * Provides basic type checking for the C subset:
 *   - int, int*, int[N] types
 *   - Type compatibility checking for assignments
 *   - Function signature validation
 *   - Array bounds checking (static where possible)
 *
 * Type errors are collected and reported; compilation continues
 * to find as many errors as possible in a single pass.
 */

#ifndef TYPECHECKER_H
#define TYPECHECKER_H

#include "ir.h"

/* Type kinds */
typedef enum {
    TYPE_INT,       /* int */
    TYPE_TRIT,      /* trit */
    TYPE_PTR,       /* int* or trit* */
    TYPE_ARRAY,     /* int[N] or trit[N] */    TYPE_TRIT_ARRAY,/* trit[N] */    TYPE_VOID,      /* void (for functions with no return) */
    TYPE_UNKNOWN    /* Unresolved type */
} TypeKind;

/* Type descriptor */
typedef struct {
    TypeKind kind;
    int array_size;  /* For TYPE_ARRAY: number of elements */
} TypeDesc;

/* Type symbol entry */
typedef struct {
    char name[64];
    TypeDesc type;
    int is_param;    /* 1 if the symbol is a function parameter */
} TypeSymbol;

#define TYPE_MAX_SYMBOLS 128

/* Type environment (scope-aware) */
typedef struct {
    TypeSymbol symbols[TYPE_MAX_SYMBOLS];
    int count;
} TypeEnv;

/* Type error entry */
typedef struct {
    char message[256];
    int node_type;  /* NodeType that caused the error */
} TypeError;

#define TYPE_MAX_ERRORS 64

/* Type checker state */
typedef struct {
    TypeEnv env;
    TypeError errors[TYPE_MAX_ERRORS];
    int error_count;
} TypeChecker;

/* Initialize a type checker */
void typechecker_init(TypeChecker *tc);

/* Run type checking on an AST. Returns 0 if no errors, error count otherwise. */
int typechecker_check(TypeChecker *tc, Expr *ast);

/* Add a type symbol to the environment */
void typechecker_add_symbol(TypeChecker *tc, const char *name, TypeDesc type);

/* Look up a type symbol. Returns NULL if not found. */
const TypeSymbol *typechecker_lookup(const TypeChecker *tc, const char *name);

/* Infer the type of an expression. Returns TYPE_UNKNOWN on error. */
TypeDesc typechecker_infer(TypeChecker *tc, Expr *e);

/* Report all collected type errors to stderr */
void typechecker_report(const TypeChecker *tc);

#endif /* TYPECHECKER_H */
