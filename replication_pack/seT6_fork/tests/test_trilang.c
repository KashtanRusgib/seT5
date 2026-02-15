/**
 * @file test_trilang.c
 * @brief TriLang Test Suite — 100 assertions for triadic operations
 *
 * Tests all TriLang components:
 *   Section 1: Triadic Arithmetic (neg, add, sub, mul, min, max, consensus)
 *   Section 2: Kleene K3 Logic (and, or, not, implies, equiv)
 *   Section 3: Peirce Categories (firstness, secondness, thirdness)
 *   Section 4: Tryte Operations (from_int, to_int, neg, add, scale)
 *   Section 5: Epistemic Features (hesitate, mediate_flux, unknown propagation)
 *   Section 6: RNS Integration (forward, inverse, add, mul via {3,5,7})
 *   Section 7: Lexer (token recognition for TriLang source)
 *   Section 8: Parser + Evaluator (AST construction and tree-walking)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "trilang.h"

static int g_pass = 0, g_fail = 0;

#define TEST(cond, msg)                                                      \
    do {                                                                     \
        if (cond) {                                                          \
            printf("  %-62s [PASS]\n", msg);                                 \
            g_pass++;                                                        \
        } else {                                                             \
            printf("  %-62s [FAIL]\n", msg);                                 \
            g_fail++;                                                        \
        }                                                                    \
    } while (0)

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 1: Triadic Arithmetic (25 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_triadic_arithmetic(void)
{
    printf("\n--- Section 1: Triadic Arithmetic ---\n");

    /* 1.1–1.3: Negation */
    TEST(tri_neg(TRI_T) == TRI_P,  "1.1  neg(T) == P");
    TEST(tri_neg(TRI_O) == TRI_O,  "1.2  neg(O) == O");
    TEST(tri_neg(TRI_P) == TRI_T,  "1.3  neg(P) == T");

    /* 1.4–1.8: Addition (value component) */
    tri_result r;
    r = tri_add(TRI_O, TRI_O);
    TEST(r.value == TRI_O && r.state == TRI_O,  "1.4  add(O,O) = O, carry O");
    r = tri_add(TRI_P, TRI_O);
    TEST(r.value == TRI_P && r.state == TRI_O,  "1.5  add(P,O) = P, carry O");
    r = tri_add(TRI_T, TRI_O);
    TEST(r.value == TRI_T && r.state == TRI_O,  "1.6  add(T,O) = T, carry O");
    r = tri_add(TRI_P, TRI_P);
    TEST(r.value == TRI_T && r.state == TRI_P,  "1.7  add(P,P) = T, carry P (overflow)");
    r = tri_add(TRI_T, TRI_T);
    TEST(r.value == TRI_P && r.state == TRI_T,  "1.8  add(T,T) = P, carry T (borrow)");

    /* 1.9–1.10: Add interpretant (mediation quality) */
    r = tri_add(TRI_P, TRI_O);
    TEST(r.interpretant == TRI_P,    "1.9  add(P,O) interpretant is P (no carry)");
    r = tri_add(TRI_P, TRI_P);
    TEST(r.interpretant == TRI_O,    "1.10 add(P,P) interpretant is O (carry present)");

    /* 1.11–1.13: Subtraction */
    r = tri_sub(TRI_P, TRI_P);
    TEST(r.value == TRI_O,           "1.11 sub(P,P) = O");
    r = tri_sub(TRI_P, TRI_T);
    TEST(r.value == TRI_T && r.state == TRI_P, "1.12 sub(P,T) = T with carry P");
    r = tri_sub(TRI_T, TRI_P);
    TEST(r.value == TRI_P && r.state == TRI_T, "1.13 sub(T,P) = P with carry T");

    /* 1.14–1.17: Multiplication */
    TEST(tri_mul(TRI_P, TRI_P) == TRI_P,   "1.14 mul(P,P) = P");
    TEST(tri_mul(TRI_T, TRI_T) == TRI_P,   "1.15 mul(T,T) = P");
    TEST(tri_mul(TRI_P, TRI_T) == TRI_T,   "1.16 mul(P,T) = T");
    TEST(tri_mul(TRI_O, TRI_P) == TRI_O,   "1.17 mul(O,P) = O (absorbing)");

    /* 1.18–1.20: Min (triadic AND gate) */
    TEST(tri_min(TRI_P, TRI_T) == TRI_T,   "1.18 min(P,T) = T");
    TEST(tri_min(TRI_O, TRI_T) == TRI_T,   "1.19 min(O,T) = T");
    TEST(tri_min(TRI_P, TRI_P) == TRI_P,   "1.20 min(P,P) = P");

    /* 1.21–1.23: Max (triadic OR gate) */
    TEST(tri_max(TRI_T, TRI_P) == TRI_P,   "1.21 max(T,P) = P");
    TEST(tri_max(TRI_O, TRI_P) == TRI_P,   "1.22 max(O,P) = P");
    TEST(tri_max(TRI_T, TRI_T) == TRI_T,   "1.23 max(T,T) = T");

    /* 1.24–1.25: Consensus (triadic majority) */
    TEST(tri_consensus(TRI_P, TRI_P, TRI_P) == TRI_P, "1.24 consensus(P,P,P) = P");
    TEST(tri_consensus(TRI_P, TRI_T, TRI_O) == TRI_O, "1.25 consensus(P,T,O) = O (no agreement)");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 2: Kleene K3 Logic (20 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_kleene_k3(void)
{
    printf("\n--- Section 2: Kleene K3 Logic ---\n");

    /* K3 AND truth table (9 entries, sample 6 + extras) */
    TEST(tri_kleene_and(TRI_P, TRI_P) == TRI_P, "2.1  K3 AND(P,P) = P");
    TEST(tri_kleene_and(TRI_P, TRI_O) == TRI_O, "2.2  K3 AND(P,O) = O (unknown propagates)");
    TEST(tri_kleene_and(TRI_P, TRI_T) == TRI_T, "2.3  K3 AND(P,T) = T (false dominates)");
    TEST(tri_kleene_and(TRI_O, TRI_O) == TRI_O, "2.4  K3 AND(O,O) = O");
    TEST(tri_kleene_and(TRI_O, TRI_T) == TRI_T, "2.5  K3 AND(O,T) = T (false dominates)");
    TEST(tri_kleene_and(TRI_T, TRI_T) == TRI_T, "2.6  K3 AND(T,T) = T");

    /* K3 OR truth table */
    TEST(tri_kleene_or(TRI_P, TRI_P) == TRI_P, "2.7  K3 OR(P,P) = P");
    TEST(tri_kleene_or(TRI_P, TRI_O) == TRI_P, "2.8  K3 OR(P,O) = P (true dominates)");
    TEST(tri_kleene_or(TRI_P, TRI_T) == TRI_P, "2.9  K3 OR(P,T) = P");
    TEST(tri_kleene_or(TRI_O, TRI_O) == TRI_O, "2.10 K3 OR(O,O) = O");
    TEST(tri_kleene_or(TRI_O, TRI_T) == TRI_O, "2.11 K3 OR(O,T) = O (unknown propagates)");
    TEST(tri_kleene_or(TRI_T, TRI_T) == TRI_T, "2.12 K3 OR(T,T) = T");

    /* K3 NOT */
    TEST(tri_kleene_not(TRI_P) == TRI_T, "2.13 K3 NOT(P) = T");
    TEST(tri_kleene_not(TRI_O) == TRI_O, "2.14 K3 NOT(O) = O (unknown fixed point)");
    TEST(tri_kleene_not(TRI_T) == TRI_P, "2.15 K3 NOT(T) = P");

    /* K3 IMPLIES: max(-a, b) */
    TEST(tri_kleene_implies(TRI_P, TRI_P) == TRI_P, "2.16 K3 P→P = P");
    TEST(tri_kleene_implies(TRI_P, TRI_T) == TRI_T, "2.17 K3 P→T = T");
    TEST(tri_kleene_implies(TRI_T, TRI_P) == TRI_P, "2.18 K3 T→P = P (ex falso quodlibet)");
    TEST(tri_kleene_implies(TRI_O, TRI_P) == TRI_P, "2.19 K3 O→P = P");
    TEST(tri_kleene_implies(TRI_O, TRI_O) == TRI_O, "2.20 K3 O→O = O");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 3: Peirce Categories (12 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_peirce_categories(void)
{
    printf("\n--- Section 3: Peirce Categories ---\n");

    /* Classification */
    TEST(tri_classify_peirce(TRI_O) == PEIRCE_FIRSTNESS,
         "3.1  O classifies as Firstness (possibility)");
    TEST(tri_classify_peirce(TRI_T) == PEIRCE_SECONDNESS,
         "3.2  T classifies as Secondness (reaction)");
    TEST(tri_classify_peirce(TRI_P) == PEIRCE_THIRDNESS,
         "3.3  P classifies as Thirdness (mediation)");

    /* Category predicates */
    TEST(tri_firstness(TRI_O) == 1,   "3.4  firstness(O) = 1");
    TEST(tri_firstness(TRI_P) == 0,   "3.5  firstness(P) = 0");
    TEST(tri_secondness(TRI_T) == 1,  "3.6  secondness(T) = 1");
    TEST(tri_secondness(TRI_O) == 0,  "3.7  secondness(O) = 0");
    TEST(tri_thirdness(TRI_P) == 1,   "3.8  thirdness(P) = 1");
    TEST(tri_thirdness(TRI_T) == 0,   "3.9  thirdness(T) = 0");

    /* Clamp */
    TEST(tri_clamp(-5) == TRI_T,      "3.10 clamp(-5) = T");
    TEST(tri_clamp(0) == TRI_O,       "3.11 clamp(0) = O");
    TEST(tri_clamp(99) == TRI_P,      "3.12 clamp(99) = P");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 4: Tryte Operations (13 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_tryte_ops(void)
{
    printf("\n--- Section 4: Tryte Operations ---\n");
    tri_tryte t;

    /* from_int / to_int roundtrip */
    tri_tryte_from_int(&t, 0);
    TEST(tri_tryte_to_int(&t) == 0,     "4.1  tryte(0) roundtrip");
    tri_tryte_from_int(&t, 1);
    TEST(tri_tryte_to_int(&t) == 1,     "4.2  tryte(1) roundtrip");
    tri_tryte_from_int(&t, -1);
    TEST(tri_tryte_to_int(&t) == -1,    "4.3  tryte(-1) roundtrip");
    tri_tryte_from_int(&t, 42);
    TEST(tri_tryte_to_int(&t) == 42,    "4.4  tryte(42) roundtrip");
    tri_tryte_from_int(&t, -42);
    TEST(tri_tryte_to_int(&t) == -42,   "4.5  tryte(-42) roundtrip");
    tri_tryte_from_int(&t, 364);
    TEST(tri_tryte_to_int(&t) == 364,   "4.6  tryte(364) max value");
    tri_tryte_from_int(&t, -364);
    TEST(tri_tryte_to_int(&t) == -364,  "4.7  tryte(-364) min value");

    /* Validity */
    tri_tryte_from_int(&t, 100);
    TEST(tri_tryte_valid(&t) == 1,      "4.8  tryte(100) is valid");

    /* Negation */
    tri_tryte a, b;
    tri_tryte_from_int(&a, 13);
    tri_tryte_neg(&a, &b);
    TEST(tri_tryte_to_int(&b) == -13,   "4.9  tryte_neg(13) = -13");

    /* Addition */
    tri_tryte c, out;
    tri_tryte_from_int(&a, 10);
    tri_tryte_from_int(&c, 20);
    tri_tryte_add(&a, &c, &out);
    TEST(tri_tryte_to_int(&out) == 30,  "4.10 tryte_add(10,20) = 30");

    tri_tryte_from_int(&a, 200);
    tri_tryte_from_int(&c, -50);
    tri_tryte_add(&a, &c, &out);
    TEST(tri_tryte_to_int(&out) == 150, "4.11 tryte_add(200,-50) = 150");

    /* Scale */
    tri_tryte_from_int(&a, 7);
    tri_tryte_scale(&a, TRI_P, &out);
    TEST(tri_tryte_to_int(&out) == 7,   "4.12 tryte_scale(7, P) = 7");
    tri_tryte_scale(&a, TRI_T, &out);
    TEST(tri_tryte_to_int(&out) == -7,  "4.13 tryte_scale(7, T) = -7");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 5: Epistemic Features (10 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_epistemic(void)
{
    printf("\n--- Section 5: Epistemic Features ---\n");

    /* Hesitation */
    TEST(tri_hesitate(TRI_O) == 1,   "5.1  hesitate(O) = 1 (epistemic pause)");
    TEST(tri_hesitate(TRI_P) == 0,   "5.2  hesitate(P) = 0 (definite)");
    TEST(tri_hesitate(TRI_T) == 0,   "5.3  hesitate(T) = 0 (definite)");

    /* Unknown propagation */
    TEST(tri_propagate_unknown(TRI_P, TRI_O) == TRI_O,
         "5.4  propagate_unknown(P,O) = O");
    TEST(tri_propagate_unknown(TRI_P, TRI_P) == TRI_P,
         "5.5  propagate_unknown(P,P) = P (both definite)");

    /* Mediate flux */
    tri_result r;
    r = tri_mediate_flux(TRI_P, TRI_P);
    TEST(r.value == TRI_O && r.state == TRI_P && r.interpretant == TRI_P,
         "5.6  flux(P,P) = (O,P,P) stable, perfect mediation");

    r = tri_mediate_flux(TRI_T, TRI_P);
    TEST(r.value == TRI_P,           "5.7  flux(T,P) delta = P (positive change)");
    TEST(r.state == TRI_O,           "5.8  flux(T,P) state = O (disagreement)");
    TEST(r.interpretant == TRI_T,    "5.9  flux(T,P) interpretant = T (degraded)");

    r = tri_mediate_flux(TRI_O, TRI_P);
    TEST(r.interpretant == TRI_O,    "5.10 flux(O,P) interpretant = O (partial)");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 6: RNS Integration (10 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_rns_integration(void)
{
    printf("\n--- Section 6: RNS Integration ---\n");

    int ra[3], rb[3], rc[3];

    /* Forward transform */
    tri_rns_forward(10, ra);
    TEST(ra[0] == 1 && ra[1] == 0 && ra[2] == 3,
         "6.1  rns_forward(10) = {1,0,3} mod {3,5,7}");

    tri_rns_forward(0, ra);
    TEST(ra[0] == 0 && ra[1] == 0 && ra[2] == 0,
         "6.2  rns_forward(0) = {0,0,0}");

    /* Inverse transform (CRT) */
    ra[0] = 1; ra[1] = 0; ra[2] = 3;
    TEST(tri_rns_inverse(ra) == 10,  "6.3  rns_inverse({1,0,3}) = 10");

    ra[0] = 0; ra[1] = 0; ra[2] = 0;
    TEST(tri_rns_inverse(ra) == 0,   "6.4  rns_inverse({0,0,0}) = 0");

    /* RNS addition (carry-free) */
    tri_rns_forward(7, ra);
    tri_rns_forward(8, rb);
    tri_rns_add(ra, rb, rc);
    TEST(tri_rns_inverse(rc) == 15,  "6.5  rns_add(7,8) = 15 (carry-free)");

    /* RNS multiplication (carry-free) */
    tri_rns_forward(3, ra);
    tri_rns_forward(4, rb);
    tri_rns_mul(ra, rb, rc);
    TEST(tri_rns_inverse(rc) == 12,  "6.6  rns_mul(3,4) = 12 (carry-free)");

    /* Moduli validation */
    TEST(TRI_RNS_MODULI[0] == 3,    "6.7  moduli[0] = 3");
    TEST(TRI_RNS_MODULI[1] == 5,    "6.8  moduli[1] = 5");
    TEST(TRI_RNS_MODULI[2] == 7,    "6.9  moduli[2] = 7");

    /* Roundtrip: larger number */
    tri_rns_forward(42, ra);
    TEST(tri_rns_inverse(ra) == 42,  "6.10 rns roundtrip(42) = 42");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 7: Lexer (5 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_lexer(void)
{
    printf("\n--- Section 7: Lexer ---\n");
    tri_token tokens[32];
    int n;

    /* Trit literals */
    n = tri_tokenize("T O P", tokens, 32);
    TEST(n >= 3 && tokens[0].type == TK_TRIT_T,  "7.1  lex 'T' → TK_TRIT_T");
    TEST(tokens[1].type == TK_TRIT_O,             "7.2  lex 'O' → TK_TRIT_O");
    TEST(tokens[2].type == TK_TRIT_P,             "7.3  lex 'P' → TK_TRIT_P");

    /* Keywords and operators */
    n = tri_tokenize("let x = P + T;", tokens, 32);
    TEST(n >= 6 && tokens[0].type == TK_LET,      "7.4  lex 'let' → TK_LET");
    TEST(tokens[4].type == TK_PLUS,                "7.5  lex '+' → TK_PLUS");
}

/* ═══════════════════════════════════════════════════════════════════════
 *  Section 8: Parser + Evaluator (5 assertions)
 * ═══════════════════════════════════════════════════════════════════════ */
static void test_parser_eval(void)
{
    printf("\n--- Section 8: Parser + Evaluator ---\n");
    tri_token tokens[64];
    tri_parser parser;
    tri_env env;
    tri_result r;

    /* Simple expression: P + T → T with carry P */
    int n = tri_tokenize("P + T;", tokens, 64);
    tri_parser_init(&parser, tokens, n);
    tri_ast_node *expr = tri_parse_expr(&parser);
    tri_env_init(&env);
    r = tri_eval(&env, expr);
    TEST(r.value == TRI_O,  "8.1  eval 'P + T' = O (1 + -1 = 0)");
    tri_ast_free(expr);

    /* Let binding + reference */
    n = tri_tokenize("let x = P; x;", tokens, 64);
    tri_parser_init(&parser, tokens, n);
    tri_env_init(&env);
    tri_ast_node *prog = tri_parse_program(&parser);
    r = tri_eval(&env, prog);
    TEST(r.value == TRI_P,  "8.2  eval 'let x = P; x' → P");
    tri_ast_free(prog);

    /* Kleene AND via & operator */
    n = tri_tokenize("P & T;", tokens, 64);
    tri_parser_init(&parser, tokens, n);
    tri_env_init(&env);
    expr = tri_parse_expr(&parser);
    r = tri_eval(&env, expr);
    TEST(r.value == TRI_T,  "8.3  eval 'P & T' = T (Kleene AND)");
    tri_ast_free(expr);

    /* If-else-mediate */
    n = tri_tokenize("if (O) { P; } else { T; } mediate { O; }", tokens, 64);
    tri_parser_init(&parser, tokens, n);
    tri_env_init(&env);
    tri_ast_node *stmt = tri_parse_stmt(&parser);
    r = tri_eval(&env, stmt);
    TEST(r.value == TRI_O,  "8.4  eval 'if(O)' → mediate branch (Thirdness)");
    TEST(env.mediation_count == 1, "8.5  mediation_count = 1");
    tri_ast_free(stmt);
}

/* ═══════════════════════════════════════════════════════════════════════
 *  MAIN — Run all sections
 * ═══════════════════════════════════════════════════════════════════════ */
int main(void)
{
    printf("╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  TriLang Test Suite — Ternary-First Triadic Language        ║\n");
    printf("╚══════════════════════════════════════════════════════════════╝\n");

    test_triadic_arithmetic();
    test_kleene_k3();
    test_peirce_categories();
    test_tryte_ops();
    test_epistemic();
    test_rns_integration();
    test_lexer();
    test_parser_eval();

    printf("\n════════════════════════════════════════════════════════════════\n");
    printf("TriLang Tests: %d passed, %d failed, %d total\n",
           g_pass, g_fail, g_pass + g_fail);
    printf("════════════════════════════════════════════════════════════════\n");

    return g_fail ? 1 : 0;
}
