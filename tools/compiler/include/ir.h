/*
 * ir.h - Intermediate Representation for the ternary compiler
 *
 * AST node types for expressions. Used by the optimizer pass
 * (constant folding) between parsing and codegen.
 *
 * Phase 1 (MVP): int values for correctness.
 * Phase 2+: Switch to trit arrays.
 */

#ifndef IR_H
#define IR_H

#include <stdlib.h>
#include <string.h>

/* AST node types */
typedef enum
{
    NODE_CONST,     /* Integer constant */
    NODE_VAR,       /* Variable reference */
    NODE_BINOP,     /* Binary operation */
    NODE_FUNC_DEF,  /* Function definition */
    NODE_FUNC_CALL, /* Function call */
    NODE_RETURN,    /* Return statement */
    NODE_PROGRAM,   /* Top-level program (list of functions) */
    NODE_DEREF,     /* Pointer dereference: *expr */
    NODE_ADDR_OF,   /* Address-of: &var */
    NODE_ASSIGN,    /* Assignment: lhs = rhs */
    NODE_VAR_DECL,  /* Variable declaration: int x = expr */
    /* Phase 3: Structured control flow (Setun-70/ALGOL-60 inspired) */
    NODE_IF,    /* if (condition) { body } [else { else_body }] */
    NODE_WHILE, /* while (condition) { body } */
    NODE_FOR,   /* for (init; condition; increment) { body } */
    NODE_BLOCK, /* { stmt1; stmt2; ... } — statement block */
    /* Phase 3: Arrays */
    NODE_ARRAY_DECL,   /* int arr[N] or int arr[N] = {init} */
    NODE_ARRAY_ACCESS, /* arr[index] — read */
    NODE_ARRAY_ASSIGN, /* arr[index] = expr — write */
    /* Phase 3: Trit types */
    NODE_TRIT_VAR_DECL,  /* trit x = expr */
    NODE_TRIT_ARRAY_DECL /* trit arr[N] or trit arr[N] = {init} */
} NodeType;

/* Binary operator types */
typedef enum
{
    OP_IR_ADD,
    OP_IR_MUL,
    OP_IR_SUB,
    /* Phase 3: Comparison & ternary logic ops */
    OP_IR_DIV,
    OP_IR_MOD,
    /* Phase 3: Comparison & ternary logic ops */
    OP_IR_CMP_EQ, /* a == b */
    OP_IR_CMP_LT, /* a < b */
    OP_IR_CMP_GT, /* a > b */
    OP_IR_NEG     /* Ternary negation (unary) */
} OpType;

/* Expression AST node */
typedef struct Expr
{
    NodeType type;
    int val;              /* For NODE_CONST */
    char *name;           /* For NODE_VAR, NODE_FUNC_DEF, NODE_FUNC_CALL */
    OpType op;            /* For NODE_BINOP */
    struct Expr *left;    /* For NODE_BINOP left operand / NODE_RETURN expr */
    struct Expr *right;   /* For NODE_BINOP right operand */
    struct Expr *body;    /* For NODE_FUNC_DEF / NODE_IF / NODE_WHILE / NODE_FOR body */
    struct Expr **params; /* FUNC_DEF: param list / FUNC_CALL: args / PROGRAM: funcs */
    int param_count;      /* Number of params / args / funcs */
    /* Phase 3: Structured control flow (Setun-70 inspired) */
    struct Expr *condition; /* For NODE_IF, NODE_WHILE, NODE_FOR: condition expr */
    struct Expr *else_body; /* For NODE_IF: else branch (NULL if no else) */
    struct Expr *increment; /* For NODE_FOR: increment expression */
    /* Phase 3: Arrays */
    int array_size; /* For NODE_ARRAY_DECL: number of elements */
} Expr;

/* Create a constant node */
Expr *create_const(int val);

/* Create a variable node */
Expr *create_var(const char *name);

/* Create a binary operation node */
Expr *create_binop(OpType op, Expr *left, Expr *right);

/* Optimize: constant folding pass (recursive) */
void optimize(Expr *e);

/* Create a function definition node */
Expr *create_func_def(const char *name, Expr **params, int param_count, Expr *body);

/* Create a function call node */
Expr *create_func_call(const char *name, Expr **args, int arg_count);

/* Create a return statement node */
Expr *create_return(Expr *expr);

/* Create a program node (container for function definitions) */
Expr *create_program(void);

/* Add a function definition to a program node */
void program_add_func(Expr *prog, Expr *func);

/* Create a dereference node (*expr) */
Expr *create_deref(Expr *expr);

/* Create an address-of node (&var) */
Expr *create_addr_of(Expr *var);

/* Create an assignment node (lhs = rhs) */
Expr *create_assign(Expr *lhs, Expr *rhs);

/* Create a variable declaration node (int x = expr) */
Expr *create_var_decl(const char *name, Expr *init);

/* Phase 3: Structured control flow constructors (Setun-70/ALGOL-60) */

/* Create an if node: if (cond) { body } [else { else_body }] */
Expr *create_if(Expr *cond, Expr *body, Expr *else_body);

/* Create a while node: while (cond) { body } */
Expr *create_while(Expr *cond, Expr *body);

/* Create a for node: for (init; cond; inc) { body } */
Expr *create_for(Expr *init, Expr *cond, Expr *inc, Expr *body);

/* Create a block node: { stmt1; stmt2; ... } */
Expr *create_block(void);

/* Add a statement to a block */
void block_add_stmt(Expr *block, Expr *stmt);

/* Phase 3: Array constructors */

/* Create an array declaration: int arr[size] */
Expr *create_array_decl(const char *name, int size, Expr **init_values, int init_count);

/* Create an array access: arr[index] */
Expr *create_array_access(const char *name, Expr *index);

/* Create an array assignment: arr[index] = value */
Expr *create_array_assign(const char *name, Expr *index, Expr *value);

/* Free an expression tree */
void expr_free(Expr *e);

#endif /* IR_H */
