/**
 * @file trilang.h
 * @brief TriLang — Ternary-First Programming Language with Triadic Logic
 *
 * A ternary-native language built on three foundational pillars:
 *   1. Peirce's Triads   — Firstness / Secondness / Thirdness
 *   2. Kleene K3 Logic    — True / False / Unknown (three-valued)
 *   3. Balanced Ternary   — {T=-1, O=0, P=+1}
 *
 * Core Design:
 *   - Trit literals: T (resistance, -1), O (potential, 0), P (affirmation, +1)
 *   - Tryte: 6 trits, range -(3^6-1)/2 .. +(3^6-1)/2 = -364..+364
 *   - Triadic return: every function yields (value, state, interpretant)
 *   - Epistemic: unknown propagation, hesitation reactors, mediation
 *   - RNS hooks: built-in carry-free parallel arithmetic via {3,5,7}
 *
 * Triadic Operations:
 *   neg(t) = -t
 *   add(a,b) with carry mediation → (sum, carry, mediation_state)
 *   mul(a,b) = sign(a*b)
 *   min(a,b) — active resistance (triadic AND)
 *   max(a,b) — active affirmation (triadic OR)
 *   consensus(a,b,c) — all same → that value, else Unknown
 *
 * Kleene K3 Logic:
 *   kleene_and(a,b) = min(a,b) — False dominates
 *   kleene_or(a,b) = max(a,b) — True dominates
 *   kleene_not(a) = -a
 *   kleene_implies(a,b) = max(-a, b)
 *
 * Lexer/Parser/VM:
 *   Tokenizes TriLang source → AST → tree-walking evaluator
 *   Keywords: func, returns, if, else, mediate, while, switch, case,
 *             assert, hesitate, trit, tryte, unknown
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef TRILANG_H
#define TRILANG_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ═══════════════════════════════════════════════════════════════════════
 *  1. CORE TRIT TYPE
 * ═══════════════════════════════════════════════════════════════════════ */

/** Balanced ternary trit: -1 (T), 0 (O), +1 (P) */
typedef int8_t tri_trit;

#define TRI_T  ((tri_trit)-1)  /**< Resistance / Secondness / False */
#define TRI_O  ((tri_trit) 0)  /**< Potential  / Firstness  / Unknown */
#define TRI_P  ((tri_trit)+1)  /**< Affirmation/ Thirdness  / True */

/** Clamp any integer to valid trit range */
static inline tri_trit tri_clamp(int v) {
    return (tri_trit)(v < -1 ? -1 : (v > 1 ? 1 : v));
}

/** Validate trit value */
static inline int tri_is_valid(tri_trit t) {
    return t >= -1 && t <= 1;
}

/* ═══════════════════════════════════════════════════════════════════════
 *  2. TRYTE — 6-TRIT WORD
 * ═══════════════════════════════════════════════════════════════════════ */

#define TRI_TRYTE_WIDTH  6
#define TRI_TRYTE_MAX    364   /* (3^6 - 1) / 2 */
#define TRI_TRYTE_MIN   (-364)

typedef struct {
    tri_trit trits[TRI_TRYTE_WIDTH];
} tri_tryte;

/** Convert integer to tryte (balanced ternary decomposition) */
void tri_tryte_from_int(tri_tryte *out, int value);

/** Convert tryte to integer */
int tri_tryte_to_int(const tri_tryte *t);

/** Check if all trits in tryte are valid */
int tri_tryte_valid(const tri_tryte *t);

/* ═══════════════════════════════════════════════════════════════════════
 *  3. TRIADIC RETURN TYPE (Peirce-inspired)
 * ═══════════════════════════════════════════════════════════════════════ */

/**
 * Triadic result: every TriLang operation returns three components:
 *   - value:        the computed result trit
 *   - state:        epistemic state (T=error, O=uncertain, P=confident)
 *   - interpretant: mediation quality (T=degraded, O=neutral, P=enhanced)
 */
typedef struct {
    tri_trit value;
    tri_trit state;
    tri_trit interpretant;
} tri_result;

/** Create a triadic result */
static inline tri_result tri_make_result(tri_trit v, tri_trit s, tri_trit i) {
    tri_result r = { v, s, i };
    return r;
}

/** Confident result: value with state=P, interpretant=P */
static inline tri_result tri_confident(tri_trit v) {
    return tri_make_result(v, TRI_P, TRI_P);
}

/** Uncertain result: value with state=O */
static inline tri_result tri_uncertain(tri_trit v) {
    return tri_make_result(v, TRI_O, TRI_O);
}

/** Error result: value with state=T, interpretant=T */
static inline tri_result tri_error(tri_trit v) {
    return tri_make_result(v, TRI_T, TRI_T);
}

/* ═══════════════════════════════════════════════════════════════════════
 *  4. TRIADIC ARITHMETIC OPERATIONS
 * ═══════════════════════════════════════════════════════════════════════ */

/** Negation: -t (Peircean: Secondness inversion) */
static inline tri_trit tri_neg(tri_trit t) {
    return (tri_trit)(-t);
}

/** Balanced ternary addition with triadic carry result */
tri_result tri_add(tri_trit a, tri_trit b);

/** Balanced ternary subtraction: a + neg(b) */
tri_result tri_sub(tri_trit a, tri_trit b);

/** Balanced ternary multiplication: sign(a*b) */
static inline tri_trit tri_mul(tri_trit a, tri_trit b) {
    int prod = (int)a * (int)b;
    return tri_clamp(prod);
}

/** Triadic minimum (active resistance / AND gate) */
static inline tri_trit tri_min(tri_trit a, tri_trit b) {
    return (a < b) ? a : b;
}

/** Triadic maximum (active affirmation / OR gate) */
static inline tri_trit tri_max(tri_trit a, tri_trit b) {
    return (a > b) ? a : b;
}

/** Consensus: if all three agree, return that value; else Unknown */
static inline tri_trit tri_consensus(tri_trit a, tri_trit b, tri_trit c) {
    return (a == b && b == c) ? a : TRI_O;
}

/** Absolute value */
static inline tri_trit tri_abs(tri_trit t) {
    return (t < 0) ? (tri_trit)(-t) : t;
}

/* ═══════════════════════════════════════════════════════════════════════
 *  5. KLEENE K3 THREE-VALUED LOGIC
 * ═══════════════════════════════════════════════════════════════════════ */

/** Kleene AND: min(a, b) — False dominates, Unknown propagates */
static inline tri_trit tri_kleene_and(tri_trit a, tri_trit b) {
    return tri_min(a, b);
}

/** Kleene OR: max(a, b) — True dominates, Unknown propagates */
static inline tri_trit tri_kleene_or(tri_trit a, tri_trit b) {
    return tri_max(a, b);
}

/** Kleene NOT: -a */
static inline tri_trit tri_kleene_not(tri_trit a) {
    return tri_neg(a);
}

/** Kleene IMPLIES: max(-a, b) — material implication */
static inline tri_trit tri_kleene_implies(tri_trit a, tri_trit b) {
    return tri_max(tri_neg(a), b);
}

/** Kleene EQUIV: and(implies(a,b), implies(b,a)) */
static inline tri_trit tri_kleene_equiv(tri_trit a, tri_trit b) {
    return tri_kleene_and(tri_kleene_implies(a, b),
                          tri_kleene_implies(b, a));
}

/* ═══════════════════════════════════════════════════════════════════════
 *  6. PEIRCE CATEGORY CLASSIFICATION
 * ═══════════════════════════════════════════════════════════════════════ */

/** Peirce category enumeration */
typedef enum {
    PEIRCE_FIRSTNESS  = -1,  /**< Quality, possibility, potential */
    PEIRCE_SECONDNESS =  0,  /**< Brute fact, reaction, resistance */
    PEIRCE_THIRDNESS  =  1   /**< Law, mediation, habit */
} tri_peirce_category;

/** Classify a trit as a Peirce category */
static inline tri_peirce_category tri_classify_peirce(tri_trit t) {
    if (t == TRI_O) return PEIRCE_FIRSTNESS;
    if (t == TRI_T) return PEIRCE_SECONDNESS;
    return PEIRCE_THIRDNESS;
}

/** Category ground: Firstness — pure quality (returns abs(t) as quality strength) */
static inline int tri_firstness(tri_trit t) {
    return (t == TRI_O) ? 1 : 0;
}

/** Category correlate: Secondness — dyadic reaction (T indicates resistance) */
static inline int tri_secondness(tri_trit t) {
    return (t == TRI_T) ? 1 : 0;
}

/** Category mediate: Thirdness — triadic law (P indicates mediation) */
static inline int tri_thirdness(tri_trit t) {
    return (t == TRI_P) ? 1 : 0;
}

/* ═══════════════════════════════════════════════════════════════════════
 *  7. EPISTEMIC FEATURES
 * ═══════════════════════════════════════════════════════════════════════ */

/** Hesitation: returns 1 if trit is Unknown (epistemic pause) */
static inline int tri_hesitate(tri_trit t) {
    return (t == TRI_O) ? 1 : 0;
}

/**
 * Mediate flux: Peircean mediation between previous and current state.
 *   Returns triadic result:
 *     value:        delta (change direction)
 *     state:        mediated consensus
 *     interpretant: interpretation quality
 */
tri_result tri_mediate_flux(tri_trit prev, tri_trit curr);

/**
 * Unknown propagation: if any input is Unknown, result is Unknown.
 * Models epistemic uncertainty through computation.
 */
static inline tri_trit tri_propagate_unknown(tri_trit a, tri_trit b) {
    if (a == TRI_O || b == TRI_O) return TRI_O;
    return a;  /* both definite — return first */
}

/* ═══════════════════════════════════════════════════════════════════════
 *  8. TRYTE ARITHMETIC (6-trit balanced ternary)
 * ═══════════════════════════════════════════════════════════════════════ */

/** Add two trytes, return triadic result (sum_int, carry_state, overflow_flag) */
tri_result tri_tryte_add(const tri_tryte *a, const tri_tryte *b, tri_tryte *out);

/** Negate a tryte (flip all trits) */
void tri_tryte_neg(const tri_tryte *in, tri_tryte *out);

/** Multiply tryte by single trit (scale by T/O/P) */
void tri_tryte_scale(const tri_tryte *in, tri_trit scalar, tri_tryte *out);

/* ═══════════════════════════════════════════════════════════════════════
 *  9. RNS INTEGRATION HOOKS
 * ═══════════════════════════════════════════════════════════════════════ */

#define TRI_RNS_MODULI_COUNT  3
extern const int TRI_RNS_MODULI[TRI_RNS_MODULI_COUNT];  /* {3, 5, 7} */

/** RNS forward transform: integer → residues mod {3,5,7} */
void tri_rns_forward(int value, int residues[TRI_RNS_MODULI_COUNT]);

/** RNS inverse transform: residues → integer via CRT */
int tri_rns_inverse(const int residues[TRI_RNS_MODULI_COUNT]);

/** RNS carry-free addition: per-channel mod add */
void tri_rns_add(const int a[TRI_RNS_MODULI_COUNT],
                 const int b[TRI_RNS_MODULI_COUNT],
                 int out[TRI_RNS_MODULI_COUNT]);

/** RNS carry-free multiplication: per-channel mod mul */
void tri_rns_mul(const int a[TRI_RNS_MODULI_COUNT],
                 const int b[TRI_RNS_MODULI_COUNT],
                 int out[TRI_RNS_MODULI_COUNT]);

/* ═══════════════════════════════════════════════════════════════════════
 * 10. LEXER — TOKEN TYPES
 * ═══════════════════════════════════════════════════════════════════════ */

typedef enum {
    /* Literals */
    TK_TRIT_T,       /**< T literal (-1) */
    TK_TRIT_O,       /**< O literal (0) */
    TK_TRIT_P,       /**< P literal (+1) */
    TK_INT,          /**< Integer literal */

    /* Keywords */
    TK_FUNC,         /**< func */
    TK_RETURNS,      /**< returns */
    TK_IF,           /**< if */
    TK_ELSE,         /**< else */
    TK_MEDIATE,      /**< mediate */
    TK_WHILE,        /**< while */
    TK_SWITCH,       /**< switch */
    TK_CASE,         /**< case */
    TK_ASSERT,       /**< assert */
    TK_HESITATE,     /**< hesitate */
    TK_TRIT_KW,      /**< trit (type keyword) */
    TK_TRYTE_KW,     /**< tryte (type keyword) */
    TK_UNKNOWN_KW,   /**< unknown */
    TK_LET,          /**< let */

    /* Operators */
    TK_PLUS,         /**< + */
    TK_MINUS,        /**< - */
    TK_STAR,         /**< * */
    TK_BANG,         /**< ! (negation) */
    TK_AMP,          /**< & (Kleene AND) */
    TK_PIPE,         /**< | (Kleene OR) */
    TK_ARROW,        /**< -> */
    TK_EQ,           /**< == */
    TK_NEQ,          /**< != */
    TK_ASSIGN,       /**< = */

    /* Delimiters */
    TK_LPAREN,       /**< ( */
    TK_RPAREN,       /**< ) */
    TK_LBRACE,       /**< { */
    TK_RBRACE,       /**< } */
    TK_COMMA,        /**< , */
    TK_SEMI,         /**< ; */
    TK_COLON,        /**< : */

    /* Identifiers */
    TK_IDENT,        /**< user identifier */

    /* Control */
    TK_EOF,          /**< end-of-input */
    TK_ERROR         /**< lexer error */
} tri_token_type;

/** Token with type, string value, and source position */
typedef struct {
    tri_token_type type;
    char           text[64];
    int            int_val;    /**< for TK_INT tokens */
    int            line;
    int            col;
} tri_token;

#define TRI_MAX_TOKENS 256

/** Lexer state */
typedef struct {
    const char *source;
    size_t      pos;
    int         line;
    int         col;
} tri_lexer;

/** Initialize lexer with source string */
void tri_lexer_init(tri_lexer *lex, const char *source);

/** Get next token */
tri_token tri_lexer_next(tri_lexer *lex);

/** Tokenize entire source into array, returns count */
int tri_tokenize(const char *source, tri_token tokens[], int max_tokens);

/* ═══════════════════════════════════════════════════════════════════════
 * 11. AST — ABSTRACT SYNTAX TREE
 * ═══════════════════════════════════════════════════════════════════════ */

typedef enum {
    AST_TRIT_LIT,     /**< Trit literal (T, O, P) */
    AST_INT_LIT,      /**< Integer literal */
    AST_IDENT,        /**< Variable reference */
    AST_UNARY,        /**< Unary op (neg, not, hesitate) */
    AST_BINARY,       /**< Binary op (+, -, *, &, |, ==, !=) */
    AST_CALL,         /**< Function call */
    AST_IF,           /**< If-else-mediate */
    AST_WHILE,        /**< While loop */
    AST_SWITCH,       /**< Triadic switch (T/O/P cases) */
    AST_LET,          /**< Let binding */
    AST_FUNC,         /**< Function definition */
    AST_BLOCK,        /**< Block of statements */
    AST_ASSERT,       /**< Assert statement */
    AST_RETURN        /**< Return triadic result */
} tri_ast_type;

#define TRI_AST_MAX_CHILDREN  8

typedef struct tri_ast_node {
    tri_ast_type type;
    tri_trit     trit_val;     /**< for AST_TRIT_LIT */
    int          int_val;      /**< for AST_INT_LIT */
    char         name[64];     /**< for AST_IDENT, AST_FUNC, AST_CALL */
    int          op;           /**< operator token type for UNARY/BINARY */
    struct tri_ast_node *children[TRI_AST_MAX_CHILDREN];
    int          child_count;
} tri_ast_node;

/** Allocate and initialize a new AST node */
tri_ast_node *tri_ast_new(tri_ast_type type);

/** Free an AST node and all children recursively */
void tri_ast_free(tri_ast_node *node);

/** Add a child to an AST node */
int tri_ast_add_child(tri_ast_node *parent, tri_ast_node *child);

/* ═══════════════════════════════════════════════════════════════════════
 * 12. PARSER
 * ═══════════════════════════════════════════════════════════════════════ */

typedef struct {
    tri_token *tokens;
    int        count;
    int        pos;
} tri_parser;

/** Initialize parser with token array */
void tri_parser_init(tri_parser *p, tri_token tokens[], int count);

/** Parse an expression */
tri_ast_node *tri_parse_expr(tri_parser *p);

/** Parse a statement */
tri_ast_node *tri_parse_stmt(tri_parser *p);

/** Parse a complete program (sequence of statements) */
tri_ast_node *tri_parse_program(tri_parser *p);

/* ═══════════════════════════════════════════════════════════════════════
 * 13. EVALUATOR (Tree-walking interpreter)
 * ═══════════════════════════════════════════════════════════════════════ */

#define TRI_ENV_MAX_VARS 64

typedef struct {
    char     name[64];
    tri_trit value;
} tri_var;

typedef struct {
    tri_var vars[TRI_ENV_MAX_VARS];
    int     var_count;
    int     hesitation_count;  /**< Number of hesitate() triggers */
    int     mediation_count;   /**< Number of mediation steps */
} tri_env;

/** Initialize evaluation environment */
void tri_env_init(tri_env *env);

/** Set a variable */
int tri_env_set(tri_env *env, const char *name, tri_trit value);

/** Get a variable (returns TRI_O if not found — epistemic default) */
tri_trit tri_env_get(tri_env *env, const char *name);

/** Evaluate an AST node in the given environment */
tri_result tri_eval(tri_env *env, tri_ast_node *node);

#ifdef __cplusplus
}
#endif

#endif /* TRILANG_H */
