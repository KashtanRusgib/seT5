/*
 * typechecker.c - Type Checking Implementation (Phase 3)
 *
 * Walks the AST and performs type inference/checking.
 * Reports type errors without stopping compilation.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include "../include/typechecker.h"
#include "../include/logger.h"

void typechecker_init(TypeChecker *tc) {
    tc->env.count = 0;
    tc->error_count = 0;
}

static void tc_error(TypeChecker *tc, int node_type, const char *fmt, ...) {
    if (tc->error_count >= TYPE_MAX_ERRORS) return;
    TypeError *err = &tc->errors[tc->error_count++];
    err->node_type = node_type;

    va_list args;
    va_start(args, fmt);
    vsnprintf(err->message, sizeof(err->message), fmt, args);
    va_end(args);
}

void typechecker_add_symbol(TypeChecker *tc, const char *name, TypeDesc type) {
    if (tc->env.count >= TYPE_MAX_SYMBOLS) return;
    TypeSymbol *sym = &tc->env.symbols[tc->env.count++];
    strncpy(sym->name, name, 63);
    sym->name[63] = '\0';
    sym->type = type;
    sym->is_param = 0;
}

const TypeSymbol *typechecker_lookup(const TypeChecker *tc, const char *name) {
    /* Search from end (most recent scope first) */
    for (int i = tc->env.count - 1; i >= 0; i--) {
        if (strcmp(tc->env.symbols[i].name, name) == 0) {
            return &tc->env.symbols[i];
        }
    }
    return NULL;
}

TypeDesc typechecker_infer(TypeChecker *tc, Expr *e) {
    TypeDesc unknown = {TYPE_UNKNOWN, 0};
    TypeDesc int_type = {TYPE_INT, 0};

    if (e == NULL) return unknown;

    switch (e->type) {
        case NODE_CONST:
            return int_type;

        case NODE_VAR: {
            const TypeSymbol *sym = typechecker_lookup(tc, e->name);
            if (sym == NULL) {
                tc_error(tc, e->type, "undeclared variable '%s'", e->name);
                return unknown;
            }
            return sym->type;
        }

        case NODE_BINOP: {
            TypeDesc lt = typechecker_infer(tc, e->left);
            TypeDesc rt = typechecker_infer(tc, e->right);

            /* Arithmetic and comparison require int operands */
            if (lt.kind != TYPE_INT && lt.kind != TYPE_UNKNOWN) {
                tc_error(tc, e->type, "left operand of binary op is not int");
            }
            if (rt.kind != TYPE_INT && rt.kind != TYPE_UNKNOWN) {
                tc_error(tc, e->type, "right operand of binary op is not int");
            }

            /* Comparison ops return int (0 or 1) */
            if (e->op == OP_IR_CMP_EQ || e->op == OP_IR_CMP_LT || e->op == OP_IR_CMP_GT) {
                return int_type;
            }
            return int_type;
        }

        case NODE_DEREF: {
            TypeDesc inner = typechecker_infer(tc, e->left);
            if (inner.kind != TYPE_PTR && inner.kind != TYPE_UNKNOWN) {
                tc_error(tc, e->type, "dereference of non-pointer type");
            }
            return int_type;
        }

        case NODE_ADDR_OF: {
            if (e->left && e->left->type == NODE_VAR) {
                const TypeSymbol *sym = typechecker_lookup(tc, e->left->name);
                if (sym == NULL) {
                    tc_error(tc, e->type, "address-of undeclared variable '%s'", e->left->name);
                }
            }
            TypeDesc ptr = {TYPE_PTR, 0};
            return ptr;
        }

        case NODE_ARRAY_ACCESS: {
            const TypeSymbol *sym = typechecker_lookup(tc, e->name);
            if (sym == NULL) {
                tc_error(tc, e->type, "undeclared array '%s'", e->name);
                return unknown;
            }
            if (sym->type.kind != TYPE_ARRAY) {
                tc_error(tc, e->type, "'%s' is not an array", e->name);
            }
            /* Check index type */
            TypeDesc idx_type = typechecker_infer(tc, e->left);
            if (idx_type.kind != TYPE_INT && idx_type.kind != TYPE_UNKNOWN) {
                tc_error(tc, e->type, "array index is not an integer");
            }
            /* Static bounds check if index is constant */
            if (e->left && e->left->type == NODE_CONST && sym->type.kind == TYPE_ARRAY) {
                if (e->left->val < 0 || e->left->val >= sym->type.array_size) {
                    tc_error(tc, e->type,
                        "array index %d out of bounds for '%s' (size %d)",
                        e->left->val, e->name, sym->type.array_size);
                }
            }
            return int_type;
        }

        case NODE_ARRAY_ASSIGN: {
            const TypeSymbol *sym = typechecker_lookup(tc, e->name);
            if (sym == NULL) {
                tc_error(tc, e->type, "undeclared array '%s'", e->name);
                return unknown;
            }
            if (sym->type.kind != TYPE_ARRAY) {
                tc_error(tc, e->type, "'%s' is not an array", e->name);
            }
            /* Check index */
            TypeDesc idx_type = typechecker_infer(tc, e->left);
            if (idx_type.kind != TYPE_INT && idx_type.kind != TYPE_UNKNOWN) {
                tc_error(tc, e->type, "array index is not an integer");
            }
            /* Static bounds check */
            if (e->left && e->left->type == NODE_CONST && sym->type.kind == TYPE_ARRAY) {
                if (e->left->val < 0 || e->left->val >= sym->type.array_size) {
                    tc_error(tc, e->type,
                        "array index %d out of bounds for '%s' (size %d)",
                        e->left->val, e->name, sym->type.array_size);
                }
            }
            /* Check value type */
            typechecker_infer(tc, e->right);
            return int_type;
        }

        case NODE_FUNC_CALL:
            /* Type check arguments */
            for (int i = 0; i < e->param_count; i++) {
                typechecker_infer(tc, e->params[i]);
            }
            return int_type; /* All functions return int in our subset */

        default:
            return int_type;
    }
}

/* Recursively check an AST node */
static void check_node(TypeChecker *tc, Expr *e) {
    if (e == NULL) return;

    switch (e->type) {
        case NODE_PROGRAM:
            for (int i = 0; i < e->param_count; i++) {
                check_node(tc, e->params[i]);
            }
            break;

        case NODE_FUNC_DEF: {
            /* Add function params to env */
            int saved_count = tc->env.count;
            for (int i = 0; i < e->param_count; i++) {
                if (e->params[i] && e->params[i]->type == NODE_VAR) {
                    TypeDesc p = {TYPE_INT, 0};
                    typechecker_add_symbol(tc, e->params[i]->name, p);
                }
                /* Also process non-param statements (they come after params) */
                check_node(tc, e->params[i]);
            }
            check_node(tc, e->body);
            /* Restore scope */
            tc->env.count = saved_count;
            break;
        }

        case NODE_VAR_DECL: {
            /* Check initial value type */
            if (e->left) {
                typechecker_infer(tc, e->left);
            }
            /* Add to env */
            TypeDesc t = {TYPE_INT, 0};
            typechecker_add_symbol(tc, e->name, t);
            break;
        }

        case NODE_ARRAY_DECL: {
            /* Check initializer types */
            for (int i = 0; i < e->param_count; i++) {
                TypeDesc vt = typechecker_infer(tc, e->params[i]);
                if (vt.kind != TYPE_INT && vt.kind != TYPE_UNKNOWN) {
                    tc_error(tc, e->type, "array initializer %d is not int", i);
                }
            }
            /* Check init count vs array size */
            if (e->param_count > e->array_size) {
                tc_error(tc, e->type,
                    "too many initializers for array '%s' (size %d, got %d)",
                    e->name, e->array_size, e->param_count);
            }
            /* Add to env */
            TypeDesc t = {TYPE_ARRAY, e->array_size};
            typechecker_add_symbol(tc, e->name, t);
            break;
        }

        case NODE_ASSIGN:
            typechecker_infer(tc, e->left);
            typechecker_infer(tc, e->right);
            break;

        case NODE_ARRAY_ACCESS:
        case NODE_ARRAY_ASSIGN:
            typechecker_infer(tc, e);
            break;

        case NODE_RETURN:
            if (e->left) typechecker_infer(tc, e->left);
            break;

        case NODE_IF:
            typechecker_infer(tc, e->condition);
            check_node(tc, e->body);
            if (e->else_body) check_node(tc, e->else_body);
            break;

        case NODE_WHILE:
            typechecker_infer(tc, e->condition);
            check_node(tc, e->body);
            break;

        case NODE_FOR:
            check_node(tc, e->left);     /* init */
            typechecker_infer(tc, e->condition);
            check_node(tc, e->increment);
            check_node(tc, e->body);
            break;

        case NODE_BLOCK:
            for (int i = 0; i < e->param_count; i++) {
                check_node(tc, e->params[i]);
            }
            break;

        default:
            typechecker_infer(tc, e);
            break;
    }
}

int typechecker_check(TypeChecker *tc, Expr *ast) {
    check_node(tc, ast);
    return tc->error_count;
}

void typechecker_report(const TypeChecker *tc) {
    if (tc->error_count == 0) return;
    fprintf(stderr, "=== Type Errors (%d) ===\n", tc->error_count);
    for (int i = 0; i < tc->error_count; i++) {
        fprintf(stderr, "  [%d] %s\n", i + 1, tc->errors[i].message);
    }
}
