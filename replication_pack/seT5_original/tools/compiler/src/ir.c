/*
 * ir.c - Intermediate Representation and optimizer
 *
 * Implements AST construction and constant folding optimization.
 * Phase 1 (MVP): Uses int values for correctness.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../include/ir.h"

/* Helper: allocate and zero-init an Expr node */
static Expr *alloc_expr(void) {
    Expr *e = (Expr *)malloc(sizeof(Expr));
    if (e == NULL) {
        fprintf(stderr, "ir: malloc failed\n");
        exit(1);
    }
    e->type = NODE_CONST;
    e->val = 0;
    e->name = NULL;
    e->op = OP_IR_ADD;
    e->left = NULL;
    e->right = NULL;
    e->body = NULL;
    e->params = NULL;
    e->param_count = 0;
    e->condition = NULL;
    e->else_body = NULL;
    e->increment = NULL;
    e->array_size = 0;
    return e;
}

Expr *create_const(int val) {
    Expr *e = alloc_expr();
    e->type = NODE_CONST;
    e->val = val;
    return e;
}

Expr *create_var(const char *name) {
    Expr *e = alloc_expr();
    e->type = NODE_VAR;
    e->name = strdup(name);
    return e;
}

Expr *create_binop(OpType op, Expr *left, Expr *right) {
    Expr *e = alloc_expr();
    e->type = NODE_BINOP;
    e->op = op;
    e->left = left;
    e->right = right;
    return e;
}

void optimize(Expr *e) {
    if (e == NULL) return;

    switch (e->type) {
        case NODE_CONST:
        case NODE_VAR:
            return;

        case NODE_BINOP:
            /* Recurse into children first (bottom-up) */
            optimize(e->left);
            optimize(e->right);

            /* Fold if both children are now constants */
            if (e->left->type == NODE_CONST && e->right->type == NODE_CONST) {
                int result = 0;
                switch (e->op) {
                    case OP_IR_ADD: result = e->left->val + e->right->val; break;
                    case OP_IR_MUL: result = e->left->val * e->right->val; break;
                    case OP_IR_SUB: result = e->left->val - e->right->val; break;
                    case OP_IR_CMP_EQ: result = (e->left->val == e->right->val) ? 1 : 0; break;
                    case OP_IR_CMP_LT: result = (e->left->val < e->right->val) ? 1 : 0; break;
                    case OP_IR_CMP_GT: result = (e->left->val > e->right->val) ? 1 : 0; break;
                    case OP_IR_NEG: result = -(e->left->val); break;
                }

                /* Convert this node to a constant */
                e->type = NODE_CONST;
                e->val = result;

                /* Free children */
                expr_free(e->left);
                expr_free(e->right);
                e->left = NULL;
                e->right = NULL;
            }
            break;

        case NODE_FUNC_DEF:
            optimize(e->body);
            break;

        case NODE_FUNC_CALL:
            for (int i = 0; i < e->param_count; i++) {
                optimize(e->params[i]);
            }
            break;

        case NODE_RETURN:
            optimize(e->left);
            break;

        case NODE_PROGRAM:
            for (int i = 0; i < e->param_count; i++) {
                optimize(e->params[i]);
            }
            break;

        case NODE_DEREF:
            optimize(e->left);
            break;

        case NODE_ADDR_OF:
            /* nothing to fold */
            break;

        case NODE_ASSIGN:
            optimize(e->right);
            break;

        case NODE_VAR_DECL:
            if (e->left) optimize(e->left);
            break;

        /* Phase 3: Structured control flow */
        case NODE_IF:
            if (e->condition) optimize(e->condition);
            if (e->body) optimize(e->body);
            if (e->else_body) optimize(e->else_body);
            break;

        case NODE_WHILE:
            if (e->condition) optimize(e->condition);
            if (e->body) optimize(e->body);
            break;

        case NODE_FOR:
            if (e->left) optimize(e->left);       /* init */
            if (e->condition) optimize(e->condition);
            if (e->increment) optimize(e->increment);
            if (e->body) optimize(e->body);
            break;

        case NODE_BLOCK:
            for (int i = 0; i < e->param_count; i++) {
                optimize(e->params[i]);
            }
            break;

        case NODE_ARRAY_DECL:
            /* Optimize init values */
            for (int i = 0; i < e->param_count; i++) {
                optimize(e->params[i]);
            }
            break;

        case NODE_ARRAY_ACCESS:
            if (e->left) optimize(e->left); /* index */
            break;

        case NODE_ARRAY_ASSIGN:
            if (e->left) optimize(e->left);  /* index */
            if (e->right) optimize(e->right); /* value */
            break;
    }
}

void expr_free(Expr *e) {
    if (e == NULL) return;
    if (e->left != NULL) expr_free(e->left);
    if (e->right != NULL) expr_free(e->right);
    if (e->body != NULL) expr_free(e->body);
    if (e->condition != NULL) expr_free(e->condition);
    if (e->else_body != NULL) expr_free(e->else_body);
    if (e->increment != NULL) expr_free(e->increment);
    if (e->params != NULL) {
        for (int i = 0; i < e->param_count; i++) {
            expr_free(e->params[i]);
        }
        free(e->params);
    }
    if (e->name != NULL) free(e->name);
    free(e);
}

Expr *create_func_def(const char *name, Expr **params, int param_count, Expr *body) {
    Expr *e = alloc_expr();
    e->type = NODE_FUNC_DEF;
    e->name = strdup(name);
    e->body = body;
    e->params = params;
    e->param_count = param_count;
    return e;
}

Expr *create_func_call(const char *name, Expr **args, int arg_count) {
    Expr *e = alloc_expr();
    e->type = NODE_FUNC_CALL;
    e->name = strdup(name);
    e->params = args;
    e->param_count = arg_count;
    return e;
}

Expr *create_return(Expr *expr) {
    Expr *e = alloc_expr();
    e->type = NODE_RETURN;
    e->left = expr;
    return e;
}

Expr *create_program(void) {
    Expr *e = alloc_expr();
    e->type = NODE_PROGRAM;
    return e;
}

void program_add_func(Expr *prog, Expr *func) {
    prog->param_count++;
    prog->params = (Expr **)realloc(prog->params, prog->param_count * sizeof(Expr *));
    if (prog->params == NULL) {
        fprintf(stderr, "ir: realloc failed\n");
        exit(1);
    }
    prog->params[prog->param_count - 1] = func;
}

Expr *create_deref(Expr *expr) {
    Expr *e = alloc_expr();
    e->type = NODE_DEREF;
    e->left = expr;
    return e;
}

Expr *create_addr_of(Expr *var) {
    Expr *e = alloc_expr();
    e->type = NODE_ADDR_OF;
    e->left = var;
    return e;
}

Expr *create_assign(Expr *lhs, Expr *rhs) {
    Expr *e = alloc_expr();
    e->type = NODE_ASSIGN;
    e->left = lhs;
    e->right = rhs;
    return e;
}

Expr *create_var_decl(const char *name, Expr *init) {
    Expr *e = alloc_expr();
    e->type = NODE_VAR_DECL;
    e->name = strdup(name);
    e->left = init;
    return e;
}

/* === Phase 3: Structured control flow constructors === */

Expr *create_if(Expr *cond, Expr *body, Expr *else_body) {
    Expr *e = alloc_expr();
    e->type = NODE_IF;
    e->condition = cond;
    e->body = body;
    e->else_body = else_body;
    return e;
}

Expr *create_while(Expr *cond, Expr *body) {
    Expr *e = alloc_expr();
    e->type = NODE_WHILE;
    e->condition = cond;
    e->body = body;
    return e;
}

Expr *create_for(Expr *init, Expr *cond, Expr *inc, Expr *body) {
    Expr *e = alloc_expr();
    e->type = NODE_FOR;
    e->left = init;       /* init expression */
    e->condition = cond;
    e->increment = inc;
    e->body = body;
    return e;
}

Expr *create_block(void) {
    Expr *e = alloc_expr();
    e->type = NODE_BLOCK;
    return e;
}

void block_add_stmt(Expr *block, Expr *stmt) {
    block->param_count++;
    block->params = (Expr **)realloc(block->params, block->param_count * sizeof(Expr *));
    if (block->params == NULL) {
        fprintf(stderr, "ir: realloc failed\n");
        exit(1);
    }
    block->params[block->param_count - 1] = stmt;
}

/* === Phase 3: Array constructors === */

Expr *create_array_decl(const char *name, int size, Expr **init_values, int init_count) {
    Expr *e = alloc_expr();
    e->type = NODE_ARRAY_DECL;
    e->name = strdup(name);
    e->array_size = size;
    e->params = init_values;
    e->param_count = init_count;
    return e;
}

Expr *create_array_access(const char *name, Expr *index) {
    Expr *e = alloc_expr();
    e->type = NODE_ARRAY_ACCESS;
    e->name = strdup(name);
    e->left = index;
    return e;
}

Expr *create_array_assign(const char *name, Expr *index, Expr *value) {
    Expr *e = alloc_expr();
    e->type = NODE_ARRAY_ASSIGN;
    e->name = strdup(name);
    e->left = index;
    e->right = value;
    return e;
}
