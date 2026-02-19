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
static inline void tri_tryte_from_int(tri_tryte *out, int value);
/** Convert tryte to integer */
static inline int tri_tryte_to_int(const tri_tryte *t);
/** Check if all trits in tryte are valid */
static inline int tri_tryte_valid(const tri_tryte *t);
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
static inline void tri_tryte_neg(const tri_tryte *in, tri_tryte *out);
/** Multiply tryte by single trit (scale by T/O/P) */
static inline void tri_tryte_scale(const tri_tryte *in, tri_trit scalar, tri_tryte *out);
/* ═══════════════════════════════════════════════════════════════════════
 *  9. RNS INTEGRATION HOOKS
 * ═══════════════════════════════════════════════════════════════════════ */

#define TRI_RNS_MODULI_COUNT  3
extern const int TRI_RNS_MODULI[TRI_RNS_MODULI_COUNT];  /* {3, 5, 7} */

/** RNS forward transform: integer → residues mod {3,5,7} */
static inline void tri_rns_forward(int value, int residues[TRI_RNS_MODULI_COUNT]);
/** RNS inverse transform: residues → integer via CRT */
static inline int tri_rns_inverse(const int residues[TRI_RNS_MODULI_COUNT]);
/** RNS carry-free addition: per-channel mod add */
static inline void tri_rns_add(const int a[TRI_RNS_MODULI_COUNT],
                 const int b[TRI_RNS_MODULI_COUNT],
                 int out[TRI_RNS_MODULI_COUNT]);
/** RNS carry-free multiplication: per-channel mod mul */
static inline void tri_rns_mul(const int a[TRI_RNS_MODULI_COUNT],
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
static inline void tri_lexer_init(tri_lexer *lex, const char *source);
/** Get next token */
tri_token tri_lexer_next(tri_lexer *lex);

/** Tokenize entire source into array, returns count */
static inline int tri_tokenize(const char *source, tri_token tokens[], int max_tokens);
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
static inline void tri_ast_free(tri_ast_node *node);
/** Add a child to an AST node */
static inline int tri_ast_add_child(tri_ast_node *parent, tri_ast_node *child);
/* ═══════════════════════════════════════════════════════════════════════
 * 12. PARSER
 * ═══════════════════════════════════════════════════════════════════════ */

typedef struct {
    tri_token *tokens;
    int        count;
    int        pos;
} tri_parser;

/** Initialize parser with token array */
static inline void tri_parser_init(tri_parser *p, tri_token tokens[], int count);
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
static inline void tri_env_init(tri_env *env);
/** Set a variable */
static inline int tri_env_set(tri_env *env, const char *name, tri_trit value);
/** Get a variable (returns TRI_O if not found — epistemic default) */
tri_trit tri_env_get(tri_env *env, const char *name);

/** Evaluate an AST node in the given environment */
tri_result tri_eval(tri_env *env, tri_ast_node *node);

/* ---- Inline implementations ---- */
/**
 * @file trilang.c
 * @brief TriLang — Full Implementation
 *
 * Implements all TriLang primitives:
 *   - Triadic arithmetic (add, sub, tryte ops)
 *   - Epistemic features (mediate_flux, unknown propagation)
 *   - RNS integration (forward/inverse/add/mul via {3,5,7})
 *   - Tryte operations (balanced ternary 6-trit words)
 *   - Lexer (tokenizer for TriLang source)
 *   - Parser (recursive-descent to AST)
 *   - Evaluator (tree-walking interpreter)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <ctype.h>

/* ═══════════════════════════════════════════════════════════════════════
 *  TRIADIC ARITHMETIC
 * ═══════════════════════════════════════════════════════════════════════ */

/**
 * Balanced ternary addition with triadic carry.
 *
 *   sum_raw = a + b         (range: -2..+2)
 *   If |sum_raw| <= 1: sum = sum_raw, carry = 0
 *   If sum_raw == +2:  sum = -1, carry = +1  (carry up)
 *   If sum_raw == -2:  sum = +1, carry = -1  (borrow)
 *
 * Returns triadic result:
 *   value:        sum trit
 *   state:        carry trit (T=borrow, O=none, P=carry)
 *   interpretant: mediation quality (P if no carry, O if carried)
 */
tri_result tri_add(tri_trit a, tri_trit b)
{
    int raw = (int)a + (int)b;
    tri_trit sum, carry;

    if (raw >= -1 && raw <= 1) {
        sum = (tri_trit)raw;
        carry = TRI_O;
    } else if (raw == 2) {
        sum = TRI_T;   /* 2 in balanced ternary: -1 + carry 1 */
        carry = TRI_P;
    } else {            /* raw == -2 */
        sum = TRI_P;   /* -2 in balanced ternary: +1 + borrow -1 */
        carry = TRI_T;
    }

    tri_trit interp = (carry == TRI_O) ? TRI_P : TRI_O;
    return tri_make_result(sum, carry, interp);
}

tri_result tri_sub(tri_trit a, tri_trit b)
{
    return tri_add(a, tri_neg(b));
}

/* ═══════════════════════════════════════════════════════════════════════
 *  EPISTEMIC: MEDIATE FLUX
 * ═══════════════════════════════════════════════════════════════════════ */

/**
 * Peircean mediation between previous and current state.
 *
 *   value:        delta direction (prev→curr change)
 *   state:        mediated consensus of prev and curr
 *   interpretant: interpretation quality
 *
 * If prev == curr: stable (no change), full confidence.
 * If either is Unknown: uncertainty propagates.
 * Otherwise: delta indicates direction of change, uncertain interpretant.
 */
tri_result tri_mediate_flux(tri_trit prev, tri_trit curr)
{
    /* Delta: direction of change */
    int diff = (int)curr - (int)prev;
    tri_trit delta = tri_clamp(diff);

    /* Mediated state: consensus of prev and curr (with self-agreement) */
    tri_trit mediated;
    if (prev == curr) {
        mediated = prev;  /* stable: full agreement */
    } else if (prev == TRI_O || curr == TRI_O) {
        mediated = TRI_O; /* unknown propagates */
    } else {
        mediated = TRI_O; /* disagreement ⇒ uncertainty */
    }

    /* Interpretant: quality of mediation */
    tri_trit interp;
    if (prev == curr) {
        interp = TRI_P;  /* perfect mediation — habit formed */
    } else if (prev == TRI_O || curr == TRI_O) {
        interp = TRI_O;  /* partial — uncertainty present */
    } else {
        interp = TRI_T;  /* degraded — active conflict */
    }

    return tri_make_result(delta, mediated, interp);
}

/* ═══════════════════════════════════════════════════════════════════════
 *  TRYTE OPERATIONS (6-trit balanced ternary)
 * ═══════════════════════════════════════════════════════════════════════ */

static inline void tri_tryte_from_int(tri_tryte *out, int value)
{
    /* Clamp to valid tryte range */
    if (value > TRI_TRYTE_MAX) value = TRI_TRYTE_MAX;
    if (value < TRI_TRYTE_MIN) value = TRI_TRYTE_MIN;

    /* Balanced ternary decomposition:
     *   For each digit position, take remainder mod 3.
     *   If remainder == 2, use -1 and carry +1.
     */
    int v = value;
    for (int i = 0; i < TRI_TRYTE_WIDTH; i++) {
        int rem = ((v % 3) + 3) % 3;  /* always positive mod */
        if (rem == 0) {
            out->trits[i] = TRI_O;
        } else if (rem == 1) {
            out->trits[i] = TRI_P;
            v -= 1;
        } else { /* rem == 2 → use -1 */
            out->trits[i] = TRI_T;
            v += 1;
        }
        v /= 3;
    }
}

static inline int tri_tryte_to_int(const tri_tryte *t)
{
    int result = 0;
    int power = 1;
    for (int i = 0; i < TRI_TRYTE_WIDTH; i++) {
        result += (int)t->trits[i] * power;
        power *= 3;
    }
    return result;
}

static inline int tri_tryte_valid(const tri_tryte *t)
{
    for (int i = 0; i < TRI_TRYTE_WIDTH; i++) {
        if (!tri_is_valid(t->trits[i])) return 0;
    }
    return 1;
}

tri_result tri_tryte_add(const tri_tryte *a, const tri_tryte *b, tri_tryte *out)
{
    tri_trit carry = TRI_O;
    int overflow = 0;

    for (int i = 0; i < TRI_TRYTE_WIDTH; i++) {
        int raw = (int)a->trits[i] + (int)b->trits[i] + (int)carry;
        if (raw >= -1 && raw <= 1) {
            out->trits[i] = (tri_trit)raw;
            carry = TRI_O;
        } else if (raw >= 2) {
            out->trits[i] = (tri_trit)(raw - 3);
            carry = TRI_P;
        } else { /* raw <= -2 */
            out->trits[i] = (tri_trit)(raw + 3);
            carry = TRI_T;
        }
    }

    if (carry != TRI_O) overflow = 1;

    int sum_int = tri_tryte_to_int(out);
    tri_trit state = carry;
    tri_trit interp = overflow ? TRI_T : TRI_P;
    (void)sum_int;

    return tri_make_result(carry, state, interp);
}

static inline void tri_tryte_neg(const tri_tryte *in, tri_tryte *out)
{
    for (int i = 0; i < TRI_TRYTE_WIDTH; i++) {
        out->trits[i] = tri_neg(in->trits[i]);
    }
}

static inline void tri_tryte_scale(const tri_tryte *in, tri_trit scalar, tri_tryte *out)
{
    if (scalar == TRI_O) {
        memset(out->trits, 0, sizeof(out->trits));
    } else if (scalar == TRI_P) {
        memcpy(out->trits, in->trits, sizeof(out->trits));
    } else { /* TRI_T: negate */
        tri_tryte_neg(in, out);
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 *  RNS INTEGRATION — Carry-free parallel arithmetic via {3,5,7}
 * ═══════════════════════════════════════════════════════════════════════ */

const int TRI_RNS_MODULI[TRI_RNS_MODULI_COUNT] = { 3, 5, 7 };

static inline void tri_rns_forward(int value, int residues[TRI_RNS_MODULI_COUNT])
{
    for (int i = 0; i < TRI_RNS_MODULI_COUNT; i++) {
        int m = TRI_RNS_MODULI[i];
        residues[i] = ((value % m) + m) % m;
    }
}

static inline int tri_rns_inverse(const int residues[TRI_RNS_MODULI_COUNT])
{
    /* CRT for moduli {3, 5, 7}, M = 105 */
    /* M1=35, M2=21, M3=15 */
    /* Inverses: 35^{-1} mod 3 = 2, 21^{-1} mod 5 = 1, 15^{-1} mod 7 = 1 */
    int M = 105;
    int result = 0;
    result += residues[0] * 70;   /* 35 * 2 = 70 */
    result += residues[1] * 21;   /* 21 * 1 = 21 */
    result += residues[2] * 15;   /* 15 * 1 = 15 */
    return ((result % M) + M) % M;
}

static inline void tri_rns_add(const int a[TRI_RNS_MODULI_COUNT],
                 const int b[TRI_RNS_MODULI_COUNT],
                 int out[TRI_RNS_MODULI_COUNT])
{
    for (int i = 0; i < TRI_RNS_MODULI_COUNT; i++) {
        out[i] = (a[i] + b[i]) % TRI_RNS_MODULI[i];
    }
}

static inline void tri_rns_mul(const int a[TRI_RNS_MODULI_COUNT],
                 const int b[TRI_RNS_MODULI_COUNT],
                 int out[TRI_RNS_MODULI_COUNT])
{
    for (int i = 0; i < TRI_RNS_MODULI_COUNT; i++) {
        out[i] = (a[i] * b[i]) % TRI_RNS_MODULI[i];
    }
}

/* ═══════════════════════════════════════════════════════════════════════
 *  LEXER — Tokenizer for TriLang source
 * ═══════════════════════════════════════════════════════════════════════ */

static inline void tri_lexer_init(tri_lexer *lex, const char *source)
{
    lex->source = source;
    lex->pos = 0;
    lex->line = 1;
    lex->col = 1;
}

static char lex_peek(tri_lexer *lex)
{
    return lex->source[lex->pos];
}

static char lex_advance(tri_lexer *lex)
{
    char c = lex->source[lex->pos++];
    if (c == '\n') { lex->line++; lex->col = 1; }
    else { lex->col++; }
    return c;
}

static void lex_skip_ws(tri_lexer *lex)
{
    while (lex->source[lex->pos] &&
           (lex->source[lex->pos] == ' '  ||
            lex->source[lex->pos] == '\t' ||
            lex->source[lex->pos] == '\n' ||
            lex->source[lex->pos] == '\r')) {
        lex_advance(lex);
    }
    /* Skip line comments: // ... */
    if (lex->source[lex->pos] == '/' && lex->source[lex->pos + 1] == '/') {
        while (lex->source[lex->pos] && lex->source[lex->pos] != '\n')
            lex_advance(lex);
        lex_skip_ws(lex);
    }
}

static tri_token make_token(tri_token_type type, const char *text, int line, int col)
{
    tri_token tok;
    memset(&tok, 0, sizeof(tok));
    tok.type = type;
    tok.line = line;
    tok.col = col;
    if (text) {
        size_t len = strlen(text);
        if (len >= sizeof(tok.text)) len = sizeof(tok.text) - 1;
        memcpy(tok.text, text, len);
        tok.text[len] = '\0';
    }
    return tok;
}

typedef struct { const char *word; tri_token_type type; } keyword_entry;

static const keyword_entry KEYWORDS[] = {
    { "func",     TK_FUNC      },
    { "returns",  TK_RETURNS   },
    { "if",       TK_IF        },
    { "else",     TK_ELSE      },
    { "mediate",  TK_MEDIATE   },
    { "while",    TK_WHILE     },
    { "switch",   TK_SWITCH    },
    { "case",     TK_CASE      },
    { "assert",   TK_ASSERT    },
    { "hesitate", TK_HESITATE  },
    { "trit",     TK_TRIT_KW   },
    { "tryte",    TK_TRYTE_KW  },
    { "unknown",  TK_UNKNOWN_KW},
    { "let",      TK_LET       },
    { NULL,       TK_ERROR     }
};

tri_token tri_lexer_next(tri_lexer *lex)
{
    lex_skip_ws(lex);
    char c = lex_peek(lex);

    if (!c) return make_token(TK_EOF, "", lex->line, lex->col);

    int line = lex->line, col = lex->col;

    /* Single-character tokens */
    switch (c) {
        case '(': lex_advance(lex); return make_token(TK_LPAREN, "(", line, col);
        case ')': lex_advance(lex); return make_token(TK_RPAREN, ")", line, col);
        case '{': lex_advance(lex); return make_token(TK_LBRACE, "{", line, col);
        case '}': lex_advance(lex); return make_token(TK_RBRACE, "}", line, col);
        case ',': lex_advance(lex); return make_token(TK_COMMA,  ",", line, col);
        case ';': lex_advance(lex); return make_token(TK_SEMI,   ";", line, col);
        case ':': lex_advance(lex); return make_token(TK_COLON,  ":", line, col);
        case '+': lex_advance(lex); return make_token(TK_PLUS,   "+", line, col);
        case '*': lex_advance(lex); return make_token(TK_STAR,   "*", line, col);
        case '&': lex_advance(lex); return make_token(TK_AMP,    "&", line, col);
        case '|': lex_advance(lex); return make_token(TK_PIPE,   "|", line, col);
        default: break;
    }

    /* Two-character tokens */
    if (c == '-' && lex->source[lex->pos + 1] == '>') {
        lex_advance(lex); lex_advance(lex);
        return make_token(TK_ARROW, "->", line, col);
    }
    if (c == '-') {
        lex_advance(lex);
        return make_token(TK_MINUS, "-", line, col);
    }
    if (c == '=' && lex->source[lex->pos + 1] == '=') {
        lex_advance(lex); lex_advance(lex);
        return make_token(TK_EQ, "==", line, col);
    }
    if (c == '!' && lex->source[lex->pos + 1] == '=') {
        lex_advance(lex); lex_advance(lex);
        return make_token(TK_NEQ, "!=", line, col);
    }
    if (c == '!') {
        lex_advance(lex);
        return make_token(TK_BANG, "!", line, col);
    }
    if (c == '=') {
        lex_advance(lex);
        return make_token(TK_ASSIGN, "=", line, col);
    }

    /* Integer literals */
    if (isdigit((unsigned char)c)) {
        char buf[64];
        int len = 0;
        while (isdigit((unsigned char)lex_peek(lex)) && len < 63) {
            buf[len++] = lex_advance(lex);
        }
        buf[len] = '\0';
        tri_token tok = make_token(TK_INT, buf, line, col);
        tok.int_val = atoi(buf);
        return tok;
    }

    /* Identifiers and keywords */
    if (isalpha((unsigned char)c) || c == '_') {
        char buf[64];
        int len = 0;
        while ((isalnum((unsigned char)lex_peek(lex)) || lex_peek(lex) == '_') && len < 63) {
            buf[len++] = lex_advance(lex);
        }
        buf[len] = '\0';

        /* Check trit literals: single T, O, P when not part of longer word */
        if (len == 1 && buf[0] == 'T') return make_token(TK_TRIT_T, "T", line, col);
        if (len == 1 && buf[0] == 'O') return make_token(TK_TRIT_O, "O", line, col);
        if (len == 1 && buf[0] == 'P') return make_token(TK_TRIT_P, "P", line, col);

        /* Check keywords */
        for (int i = 0; KEYWORDS[i].word; i++) {
            if (strcmp(buf, KEYWORDS[i].word) == 0) {
                return make_token(KEYWORDS[i].type, buf, line, col);
            }
        }

        /* Regular identifier */
        return make_token(TK_IDENT, buf, line, col);
    }

    /* Unknown character — error */
    lex_advance(lex);
    return make_token(TK_ERROR, "?", line, col);
}

static inline int tri_tokenize(const char *source, tri_token tokens[], int max_tokens)
{
    tri_lexer lex;
    tri_lexer_init(&lex, source);
    int count = 0;
    while (count < max_tokens) {
        tokens[count] = tri_lexer_next(&lex);
        if (tokens[count].type == TK_EOF) {
            count++;
            break;
        }
        if (tokens[count].type == TK_ERROR) {
            count++;
            break;
        }
        count++;
    }
    return count;
}

/* ═══════════════════════════════════════════════════════════════════════
 *  AST — Construction and Destruction
 * ═══════════════════════════════════════════════════════════════════════ */

tri_ast_node *tri_ast_new(tri_ast_type type)
{
    tri_ast_node *n = (tri_ast_node *)calloc(1, sizeof(tri_ast_node));
    if (n) n->type = type;
    return n;
}

static inline void tri_ast_free(tri_ast_node *node)
{
    if (!node) return;
    for (int i = 0; i < node->child_count; i++) {
        tri_ast_free(node->children[i]);
    }
    free(node);
}

static inline int tri_ast_add_child(tri_ast_node *parent, tri_ast_node *child)
{
    if (!parent || !child) return -1;
    if (parent->child_count >= TRI_AST_MAX_CHILDREN) return -1;
    parent->children[parent->child_count++] = child;
    return 0;
}

/* ═══════════════════════════════════════════════════════════════════════
 *  PARSER — Recursive Descent
 * ═══════════════════════════════════════════════════════════════════════ */

static inline void tri_parser_init(tri_parser *p, tri_token tokens[], int count)
{
    p->tokens = tokens;
    p->count = count;
    p->pos = 0;
}

static tri_token *parser_peek(tri_parser *p)
{
    if (p->pos < p->count) return &p->tokens[p->pos];
    return NULL;
}

static tri_token *parser_advance(tri_parser *p)
{
    if (p->pos < p->count) return &p->tokens[p->pos++];
    return NULL;
}

static int parser_match(tri_parser *p, tri_token_type type)
{
    tri_token *t = parser_peek(p);
    if (t && t->type == type) {
        parser_advance(p);
        return 1;
    }
    return 0;
}

/* Forward declarations */
static tri_ast_node *parse_primary(tri_parser *p);
static tri_ast_node *parse_unary(tri_parser *p);
static tri_ast_node *parse_binary(tri_parser *p, int min_prec);

static int op_precedence(tri_token_type t)
{
    switch (t) {
        case TK_PIPE:             return 1;  /* | (OR) */
        case TK_AMP:              return 2;  /* & (AND) */
        case TK_EQ: case TK_NEQ: return 3;  /* == != */
        case TK_PLUS: case TK_MINUS: return 4;  /* + - */
        case TK_STAR:             return 5;  /* * */
        default:                  return -1;
    }
}

static tri_ast_node *parse_primary(tri_parser *p)
{
    tri_token *t = parser_peek(p);
    if (!t) return NULL;

    switch (t->type) {
        case TK_TRIT_T: {
            parser_advance(p);
            tri_ast_node *n = tri_ast_new(AST_TRIT_LIT);
            n->trit_val = TRI_T;
            return n;
        }
        case TK_TRIT_O: {
            parser_advance(p);
            tri_ast_node *n = tri_ast_new(AST_TRIT_LIT);
            n->trit_val = TRI_O;
            return n;
        }
        case TK_TRIT_P: {
            parser_advance(p);
            tri_ast_node *n = tri_ast_new(AST_TRIT_LIT);
            n->trit_val = TRI_P;
            return n;
        }
        case TK_INT: {
            parser_advance(p);
            tri_ast_node *n = tri_ast_new(AST_INT_LIT);
            n->int_val = t->int_val;
            return n;
        }
        case TK_UNKNOWN_KW: {
            parser_advance(p);
            tri_ast_node *n = tri_ast_new(AST_TRIT_LIT);
            n->trit_val = TRI_O;
            return n;
        }
        case TK_IDENT: {
            parser_advance(p);
            /* Check if it's a function call */
            if (parser_peek(p) && parser_peek(p)->type == TK_LPAREN) {
                parser_advance(p); /* consume ( */
                tri_ast_node *call = tri_ast_new(AST_CALL);
                strncpy(call->name, t->text, 63);
                /* Parse arguments */
                while (parser_peek(p) && parser_peek(p)->type != TK_RPAREN) {
                    tri_ast_node *arg = parse_binary(p, 0);
                    if (arg) tri_ast_add_child(call, arg);
                    if (parser_peek(p) && parser_peek(p)->type == TK_COMMA) {
                        parser_advance(p);
                    }
                }
                parser_match(p, TK_RPAREN); /* consume ) */
                return call;
            }
            tri_ast_node *n = tri_ast_new(AST_IDENT);
            strncpy(n->name, t->text, 63);
            return n;
        }
        case TK_LPAREN: {
            parser_advance(p); /* consume ( */
            tri_ast_node *expr = parse_binary(p, 0);
            parser_match(p, TK_RPAREN); /* consume ) */
            return expr;
        }
        case TK_HESITATE: {
            parser_advance(p);
            parser_match(p, TK_LPAREN);
            tri_ast_node *arg = parse_binary(p, 0);
            parser_match(p, TK_RPAREN);
            tri_ast_node *n = tri_ast_new(AST_UNARY);
            n->op = TK_HESITATE;
            tri_ast_add_child(n, arg);
            return n;
        }
        default:
            return NULL;
    }
}

static tri_ast_node *parse_unary(tri_parser *p)
{
    tri_token *t = parser_peek(p);
    if (t && (t->type == TK_MINUS || t->type == TK_BANG)) {
        parser_advance(p);
        tri_ast_node *operand = parse_unary(p);
        tri_ast_node *n = tri_ast_new(AST_UNARY);
        n->op = t->type;
        tri_ast_add_child(n, operand);
        return n;
    }
    return parse_primary(p);
}

static tri_ast_node *parse_binary(tri_parser *p, int min_prec)
{
    tri_ast_node *left = parse_unary(p);
    if (!left) return NULL;

    while (1) {
        tri_token *t = parser_peek(p);
        if (!t) break;
        int prec = op_precedence(t->type);
        if (prec < min_prec) break;

        int op = t->type;
        parser_advance(p);
        tri_ast_node *right = parse_binary(p, prec + 1);
        tri_ast_node *bin = tri_ast_new(AST_BINARY);
        bin->op = op;
        tri_ast_add_child(bin, left);
        tri_ast_add_child(bin, right);
        left = bin;
    }
    return left;
}

tri_ast_node *tri_parse_expr(tri_parser *p)
{
    return parse_binary(p, 0);
}

tri_ast_node *tri_parse_stmt(tri_parser *p)
{
    tri_token *t = parser_peek(p);
    if (!t || t->type == TK_EOF) return NULL;

    /* let x = expr; */
    if (t->type == TK_LET) {
        parser_advance(p);
        tri_token *name = parser_advance(p);
        if (!name || name->type != TK_IDENT) return NULL;
        parser_match(p, TK_ASSIGN);
        tri_ast_node *val = tri_parse_expr(p);
        parser_match(p, TK_SEMI);

        tri_ast_node *let = tri_ast_new(AST_LET);
        strncpy(let->name, name->text, 63);
        tri_ast_add_child(let, val);
        return let;
    }

    /* assert expr; */
    if (t->type == TK_ASSERT) {
        parser_advance(p);
        tri_ast_node *expr = tri_parse_expr(p);
        parser_match(p, TK_SEMI);

        tri_ast_node *a = tri_ast_new(AST_ASSERT);
        tri_ast_add_child(a, expr);
        return a;
    }

    /* if (expr) { ... } else { ... } mediate { ... } */
    if (t->type == TK_IF) {
        parser_advance(p);
        parser_match(p, TK_LPAREN);
        tri_ast_node *cond = tri_parse_expr(p);
        parser_match(p, TK_RPAREN);

        parser_match(p, TK_LBRACE);
        tri_ast_node *then_block = tri_parse_program(p);
        parser_match(p, TK_RBRACE);

        tri_ast_node *else_block = NULL;
        tri_ast_node *mediate_block = NULL;

        if (parser_peek(p) && parser_peek(p)->type == TK_ELSE) {
            parser_advance(p);
            parser_match(p, TK_LBRACE);
            else_block = tri_parse_program(p);
            parser_match(p, TK_RBRACE);
        }

        if (parser_peek(p) && parser_peek(p)->type == TK_MEDIATE) {
            parser_advance(p);
            parser_match(p, TK_LBRACE);
            mediate_block = tri_parse_program(p);
            parser_match(p, TK_RBRACE);
        }

        tri_ast_node *ifn = tri_ast_new(AST_IF);
        tri_ast_add_child(ifn, cond);
        tri_ast_add_child(ifn, then_block ? then_block : tri_ast_new(AST_BLOCK));
        tri_ast_add_child(ifn, else_block ? else_block : tri_ast_new(AST_BLOCK));
        tri_ast_add_child(ifn, mediate_block ? mediate_block : tri_ast_new(AST_BLOCK));
        return ifn;
    }

    /* while (expr) { ... } */
    if (t->type == TK_WHILE) {
        parser_advance(p);
        parser_match(p, TK_LPAREN);
        tri_ast_node *cond = tri_parse_expr(p);
        parser_match(p, TK_RPAREN);
        parser_match(p, TK_LBRACE);
        tri_ast_node *body = tri_parse_program(p);
        parser_match(p, TK_RBRACE);

        tri_ast_node *wn = tri_ast_new(AST_WHILE);
        tri_ast_add_child(wn, cond);
        tri_ast_add_child(wn, body);
        return wn;
    }

    /* switch (expr) { case T: ... case O: ... case P: ... } */
    if (t->type == TK_SWITCH) {
        parser_advance(p);
        parser_match(p, TK_LPAREN);
        tri_ast_node *val = tri_parse_expr(p);
        parser_match(p, TK_RPAREN);
        parser_match(p, TK_LBRACE);

        tri_ast_node *sw = tri_ast_new(AST_SWITCH);
        tri_ast_add_child(sw, val);

        /* Parse up to 3 case branches */
        while (parser_peek(p) && parser_peek(p)->type == TK_CASE) {
            parser_advance(p); /* consume 'case' */
            tri_ast_node *case_val = parse_primary(p);
            parser_match(p, TK_COLON);
            tri_ast_node *case_body = tri_parse_stmt(p);
            tri_ast_node *pair = tri_ast_new(AST_BLOCK);
            tri_ast_add_child(pair, case_val);
            tri_ast_add_child(pair, case_body);
            tri_ast_add_child(sw, pair);
        }

        parser_match(p, TK_RBRACE);
        return sw;
    }

    /* Expression statement */
    tri_ast_node *expr = tri_parse_expr(p);
    parser_match(p, TK_SEMI);
    return expr;
}

tri_ast_node *tri_parse_program(tri_parser *p)
{
    tri_ast_node *block = tri_ast_new(AST_BLOCK);
    while (parser_peek(p) &&
           parser_peek(p)->type != TK_EOF &&
           parser_peek(p)->type != TK_RBRACE) {
        tri_ast_node *stmt = tri_parse_stmt(p);
        if (stmt) tri_ast_add_child(block, stmt);
        else break;
    }
    return block;
}

/* ═══════════════════════════════════════════════════════════════════════
 *  EVALUATOR — Tree-Walking Interpreter
 * ═══════════════════════════════════════════════════════════════════════ */

static inline void tri_env_init(tri_env *env)
{
    memset(env, 0, sizeof(*env));
}

static inline int tri_env_set(tri_env *env, const char *name, tri_trit value)
{
    /* Update existing */
    for (int i = 0; i < env->var_count; i++) {
        if (strcmp(env->vars[i].name, name) == 0) {
            env->vars[i].value = value;
            return 0;
        }
    }
    /* Add new */
    if (env->var_count >= TRI_ENV_MAX_VARS) return -1;
    strncpy(env->vars[env->var_count].name, name, 63);
    env->vars[env->var_count].value = value;
    env->var_count++;
    return 0;
}

tri_trit tri_env_get(tri_env *env, const char *name)
{
    for (int i = 0; i < env->var_count; i++) {
        if (strcmp(env->vars[i].name, name) == 0) {
            return env->vars[i].value;
        }
    }
    return TRI_O;  /* Unknown = epistemic default for unbound vars */
}

tri_result tri_eval(tri_env *env, tri_ast_node *node)
{
    if (!node) return tri_error(TRI_O);

    switch (node->type) {
        case AST_TRIT_LIT:
            return tri_confident(node->trit_val);

        case AST_INT_LIT:
            return tri_confident(tri_clamp(node->int_val));

        case AST_IDENT:
            return tri_confident(tri_env_get(env, node->name));

        case AST_UNARY: {
            tri_result child = tri_eval(env, node->children[0]);
            if (node->op == TK_MINUS || node->op == TK_BANG) {
                return tri_confident(tri_neg(child.value));
            }
            if (node->op == TK_HESITATE) {
                env->hesitation_count++;
                return tri_uncertain(child.value);
            }
            return child;
        }

        case AST_BINARY: {
            tri_result l = tri_eval(env, node->children[0]);
            tri_result r = tri_eval(env, node->children[1]);
            switch (node->op) {
                case TK_PLUS:  return tri_add(l.value, r.value);
                case TK_MINUS: return tri_sub(l.value, r.value);
                case TK_STAR:  return tri_confident(tri_mul(l.value, r.value));
                case TK_AMP:   return tri_confident(tri_kleene_and(l.value, r.value));
                case TK_PIPE:  return tri_confident(tri_kleene_or(l.value, r.value));
                case TK_EQ:
                    return tri_confident((l.value == r.value) ? TRI_P : TRI_T);
                case TK_NEQ:
                    return tri_confident((l.value != r.value) ? TRI_P : TRI_T);
                default:
                    return tri_error(TRI_O);
            }
        }

        case AST_LET: {
            tri_result val = tri_eval(env, node->children[0]);
            tri_env_set(env, node->name, val.value);
            return val;
        }

        case AST_ASSERT: {
            tri_result val = tri_eval(env, node->children[0]);
            /* Assert succeeds if value is P (True) */
            if (val.value == TRI_P) {
                return tri_confident(TRI_P);
            }
            return tri_error(val.value);
        }

        case AST_IF: {
            /* children: [0]=cond, [1]=then, [2]=else, [3]=mediate */
            tri_result cond = tri_eval(env, node->children[0]);
            if (cond.value == TRI_P) {
                return tri_eval(env, node->children[1]);
            } else if (cond.value == TRI_T) {
                return tri_eval(env, node->children[2]);
            } else {
                /* Unknown → mediate branch (Peirce's Thirdness) */
                env->mediation_count++;
                return tri_eval(env, node->children[3]);
            }
        }

        case AST_WHILE: {
            /* Simple bounded loop — max 100 iterations for safety */
            tri_result last = tri_uncertain(TRI_O);
            for (int i = 0; i < 100; i++) {
                tri_result cond = tri_eval(env, node->children[0]);
                if (cond.value != TRI_P) break;
                last = tri_eval(env, node->children[1]);
            }
            return last;
        }

        case AST_SWITCH: {
            /* children[0] = value, children[1..N] = case pairs */
            tri_result val = tri_eval(env, node->children[0]);
            for (int i = 1; i < node->child_count; i++) {
                tri_ast_node *pair = node->children[i];
                if (pair && pair->child_count >= 2) {
                    tri_result case_val = tri_eval(env, pair->children[0]);
                    if (case_val.value == val.value) {
                        return tri_eval(env, pair->children[1]);
                    }
                }
            }
            return tri_uncertain(TRI_O); /* no case matched */
        }

        case AST_CALL: {
            /* Built-in function dispatch */
            if (strcmp(node->name, "neg") == 0 && node->child_count >= 1) {
                tri_result a = tri_eval(env, node->children[0]);
                return tri_confident(tri_neg(a.value));
            }
            if (strcmp(node->name, "add") == 0 && node->child_count >= 2) {
                tri_result a = tri_eval(env, node->children[0]);
                tri_result b = tri_eval(env, node->children[1]);
                return tri_add(a.value, b.value);
            }
            if (strcmp(node->name, "mul") == 0 && node->child_count >= 2) {
                tri_result a = tri_eval(env, node->children[0]);
                tri_result b = tri_eval(env, node->children[1]);
                return tri_confident(tri_mul(a.value, b.value));
            }
            if (strcmp(node->name, "consensus") == 0 && node->child_count >= 3) {
                tri_result a = tri_eval(env, node->children[0]);
                tri_result b = tri_eval(env, node->children[1]);
                tri_result c = tri_eval(env, node->children[2]);
                return tri_confident(tri_consensus(a.value, b.value, c.value));
            }
            if (strcmp(node->name, "hesitate") == 0 && node->child_count >= 1) {
                tri_result a = tri_eval(env, node->children[0]);
                env->hesitation_count++;
                return tri_uncertain(a.value);
            }
            if (strcmp(node->name, "min") == 0 && node->child_count >= 2) {
                tri_result a = tri_eval(env, node->children[0]);
                tri_result b = tri_eval(env, node->children[1]);
                return tri_confident(tri_min(a.value, b.value));
            }
            if (strcmp(node->name, "max") == 0 && node->child_count >= 2) {
                tri_result a = tri_eval(env, node->children[0]);
                tri_result b = tri_eval(env, node->children[1]);
                return tri_confident(tri_max(a.value, b.value));
            }
            if (strcmp(node->name, "abs") == 0 && node->child_count >= 1) {
                tri_result a = tri_eval(env, node->children[0]);
                return tri_confident(tri_abs(a.value));
            }
            return tri_error(TRI_O); /* unknown function */
        }

        case AST_BLOCK: {
            tri_result last = tri_uncertain(TRI_O);
            for (int i = 0; i < node->child_count; i++) {
                last = tri_eval(env, node->children[i]);
            }
            return last;
        }

        case AST_FUNC:
        case AST_RETURN:
        default:
            return tri_error(TRI_O);
    }
}

#ifdef __cplusplus
}
#endif

#endif /* TRILANG_H */
