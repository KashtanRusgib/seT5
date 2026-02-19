/*==============================================================================
 * Red-Team Suite 90: Binary Reversion Attack
 *
 * Attack surface: checking that none of the 27 (3×3) operator combinations,
 * when driven only with {0,+1} (the binary subset of trits), produce results
 * that look like they came from a binary AND/OR gate rather than Kleene logic.
 * Also tests that TRIT_UNKNOWN is never silently promoted to TRUE or FALSE.
 *
 * Key insight: binary reversion means the function "forgets" about TRIT_FALSE=-1
 * and treats only {0,1} as its domain.  We prove this cannot happen by:
 *   (a) Exhaustively testing every combination that should differ between binary
 *       and Kleene semantics.
 *   (b) Verifying TRIT_FALSE always maps to -1, never to 0 or +1.
 *   (c) Verifying outputs reach TRIT_FALSE even when inputs are all non-negative.
 *
 * Tests 6252–6301 (50 assertions)
 * Target: 100 % pass (Sigma 9)
 *============================================================================*/

#include <stdio.h>
#include <stdint.h>
#include "set5/trit.h"

/* ── Test harness ────────────────────────────────────────────────────────── */
#define SECTION(name)          \
    do                         \
    {                          \
        section_name = (name); \
    } while (0)
#define TEST(desc)             \
    do                         \
    {                          \
        test_count++;          \
        current_test = (desc); \
    } while (0)
#define ASSERT(cond, msg)                                    \
    do                                                       \
    {                                                        \
        if (!(cond))                                         \
        {                                                    \
            printf("  FAIL [%d]: %s — %s (line %d)\n",       \
                   test_count, current_test, msg, __LINE__); \
            fail_count++;                                    \
            return;                                          \
        }                                                    \
    } while (0)
#define PASS()        \
    do                \
    {                 \
        pass_count++; \
    } while (0)

static int test_count = 0, pass_count = 0, fail_count = 0;
static const char *section_name = NULL;
static const char *current_test = NULL;

/* ── Section A: NOT must map -1↔+1, not 0↔1 ────────────────────────────── */
static void section_a_not_ternary(void)
{
    SECTION("A: NOT is ternary (maps -1↔+1), not binary (maps 0↔1)");

    TEST("test_6252: NOT(FALSE=-1) == TRUE=+1 — not binary 0");
    ASSERT(trit_not(TRIT_FALSE) == TRIT_TRUE,
           "NOT(-1) must be +1, not 0 (binary reversion)");
    PASS();

    TEST("test_6253: NOT(TRUE=+1) == FALSE=-1 — not binary 0");
    ASSERT(trit_not(TRIT_TRUE) == TRIT_FALSE,
           "NOT(+1) must be -1, not 0 (binary reversion)");
    PASS();

    TEST("test_6254: NOT(UNKNOWN=0) == UNKNOWN=0 — stays unknown");
    ASSERT(trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN,
           "NOT(0) must be 0");
    PASS();

    TEST("test_6255: NOT result is never the same as input for TRUE/FALSE");
    ASSERT(trit_not(TRIT_TRUE) != TRIT_TRUE, "NOT(T) != T");
    ASSERT(trit_not(TRIT_FALSE) != TRIT_FALSE, "NOT(F) != F");
    PASS();
}

/* ── Section B: AND must distinguish FALSE from UNKNOWN ─────────────────── */
static void section_b_and_distinguishes(void)
{
    SECTION("B: AND distinguishes FALSE(-1) from UNKNOWN(0)");

    TEST("test_6256: AND(UNKNOWN,TRUE)==UNKNOWN, not FALSE — binary would give 0");
    /* Binary AND(0,1)=0; Kleene AND(U,T)=U=0. Both give 0, but for DIFFERENT
     * reasons. The sentinel: AND(U,T) must NOT equal FALSE=-1. */
    ASSERT(trit_and(TRIT_UNKNOWN, TRIT_TRUE) != TRIT_FALSE,
           "AND(U,T) must not be FALSE");
    ASSERT(trit_and(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN,
           "AND(U,T) must be UNKNOWN");
    PASS();

    TEST("test_6257: AND(FALSE,UNKNOWN)==FALSE, not UNKNOWN — FALSE must dominate");
    ASSERT(trit_and(TRIT_FALSE, TRIT_UNKNOWN) == TRIT_FALSE,
           "AND(F,U) must be FALSE, FALSE dominates");
    PASS();

    TEST("test_6258: AND(FALSE,TRUE)==FALSE — binary AND(0,1)=0 but this is -1");
    ASSERT(trit_and(TRIT_FALSE, TRIT_TRUE) == TRIT_FALSE,
           "AND(F,T) must be FALSE (-1), not UNKNOWN (0)");
    ASSERT(trit_and(TRIT_FALSE, TRIT_TRUE) == (trit)-1,
           "AND(F,T) result must be -1, not 0");
    PASS();

    TEST("test_6259: AND(FALSE,FALSE)==FALSE — attack: not mistaken for binary false");
    ASSERT(trit_and(TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE,
           "AND(F,F) must be FALSE");
    ASSERT(trit_and(TRIT_FALSE, TRIT_FALSE) == (trit)-1,
           "AND(F,F) must be -1");
    PASS();

    TEST("test_6260: AND(TRUE,TRUE)==TRUE — only all-true input gives TRUE");
    ASSERT(trit_and(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE,
           "AND(T,T) must be TRUE");
    ASSERT(trit_and(TRIT_TRUE, TRIT_TRUE) == (trit) + 1,
           "AND(T,T) must be +1");
    PASS();
}

/* ── Section C: OR must distinguish TRUE from UNKNOWN ─────────────────────  */
static void section_c_or_distinguishes(void)
{
    SECTION("C: OR distinguishes TRUE(+1) from UNKNOWN(0)");

    TEST("test_6261: OR(UNKNOWN,FALSE)==UNKNOWN, not TRUE");
    ASSERT(trit_or(TRIT_UNKNOWN, TRIT_FALSE) != TRIT_TRUE,
           "OR(U,F) must not be TRUE");
    ASSERT(trit_or(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_UNKNOWN,
           "OR(U,F) must be UNKNOWN");
    PASS();

    TEST("test_6262: OR(TRUE,UNKNOWN)==TRUE — TRUE must dominate");
    ASSERT(trit_or(TRIT_TRUE, TRIT_UNKNOWN) == TRIT_TRUE,
           "OR(T,U) must be TRUE, TRUE dominates");
    PASS();

    TEST("test_6263: OR(FALSE,TRUE)==TRUE — binary OR(0,1)=1 and this is +1, not 0");
    ASSERT(trit_or(TRIT_FALSE, TRIT_TRUE) == TRIT_TRUE,
           "OR(F,T) must be TRUE (+1)");
    ASSERT(trit_or(TRIT_FALSE, TRIT_TRUE) == (trit) + 1,
           "OR(F,T) must be +1");
    PASS();

    TEST("test_6264: OR(TRUE,TRUE)==TRUE — +1, not just 1");
    ASSERT(trit_or(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE, "OR(T,T) must be TRUE");
    ASSERT(trit_or(TRIT_TRUE, TRIT_TRUE) == (trit) + 1, "OR(T,T) must be +1");
    PASS();

    TEST("test_6265: OR(FALSE,FALSE)==FALSE — -1, not 0");
    ASSERT(trit_or(TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE, "OR(F,F) must be FALSE");
    ASSERT(trit_or(TRIT_FALSE, TRIT_FALSE) == (trit)-1, "OR(F,F) must be -1");
    PASS();
}

/* ── Section D: Excluded-middle failure (Kleene property) ───────────────── */
static void section_d_excluded_middle(void)
{
    SECTION("D: Excluded middle fails for UNKNOWN (Kleene property, not binary)");

    TEST("test_6266: AND(UNKNOWN, NOT(UNKNOWN)) != TRUE — no excluded middle");
    /* Binary law: a AND (NOT a) = FALSE.
     * Kleene: U AND NOT(U) = U AND U = U ≠ FALSE, ≠ TRUE */
    trit u = TRIT_UNKNOWN;
    ASSERT(trit_and(u, trit_not(u)) == TRIT_UNKNOWN,
           "AND(U, NOT U) must be UNKNOWN, not TRUE");
    PASS();

    TEST("test_6267: OR(UNKNOWN, NOT(UNKNOWN)) != TRUE — bivalence fails");
    /* Binary law: a OR (NOT a) = TRUE.
     * Kleene: U OR NOT(U) = U OR U = U ≠ TRUE */
    ASSERT(trit_or(u, trit_not(u)) == TRIT_UNKNOWN,
           "OR(U, NOT U) must be UNKNOWN, not TRUE");
    PASS();

    TEST("test_6268: AND(FALSE, NOT(FALSE)) == FALSE (not UNKNOWN)");
    ASSERT(trit_and(TRIT_FALSE, trit_not(TRIT_FALSE)) == TRIT_FALSE,
           "AND(F, NOT F) = AND(F,T) = FALSE");
    PASS();

    TEST("test_6269: OR(TRUE, NOT(TRUE)) == TRUE (not UNKNOWN)");
    ASSERT(trit_or(TRIT_TRUE, trit_not(TRIT_TRUE)) == TRIT_TRUE,
           "OR(T, NOT T) = OR(T,F) = TRUE");
    PASS();
}

/* ── Section E: UNKNOWN propagation never silently becomes definite ──────── */
static void section_e_unknown_propagation(void)
{
    SECTION("E: UNKNOWN never promoted to TRUE or FALSE through chains");

    TEST("test_6270: AND chain with one UNKNOWN terminates at UNKNOWN not FALSE");
    {
        trit v = TRIT_TRUE;
        v = trit_and(v, TRIT_TRUE);
        v = trit_and(v, TRIT_UNKNOWN); /* inject UNKNOWN */
        v = trit_and(v, TRIT_TRUE);
        ASSERT(v == TRIT_UNKNOWN,
               "UNKNOWN in AND chain should propagate to UNKNOWN");
    }
    PASS();

    TEST("test_6271: OR chain with one UNKNOWN: UNKNOWN between FALSEs stays UNKNOWN");
    {
        trit v = TRIT_FALSE;
        v = trit_or(v, TRIT_FALSE);
        v = trit_or(v, TRIT_UNKNOWN); /* inject UNKNOWN */
        v = trit_or(v, TRIT_FALSE);
        ASSERT(v == TRIT_UNKNOWN,
               "UNKNOWN in OR chain of FALSEs must stay UNKNOWN");
    }
    PASS();

    TEST("test_6272: AND chain with FALSE terminates at FALSE even before UNKNOWN");
    {
        trit v = TRIT_TRUE;
        v = trit_and(v, TRIT_FALSE); /* FALSE dominates */
        v = trit_and(v, TRIT_UNKNOWN);
        v = trit_and(v, TRIT_TRUE);
        ASSERT(v == TRIT_FALSE, "FALSE must dominate AND chain");
    }
    PASS();

    TEST("test_6273: OR chain with TRUE terminates at TRUE even before UNKNOWN");
    {
        trit v = TRIT_FALSE;
        v = trit_or(v, TRIT_TRUE); /* TRUE dominates */
        v = trit_or(v, TRIT_UNKNOWN);
        v = trit_or(v, TRIT_FALSE);
        ASSERT(v == TRIT_TRUE, "TRUE must dominate OR chain");
    }
    PASS();

    TEST("test_6274: 50-deep AND chain: UNKNOWN at position 25 gives UNKNOWN");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 50; i++)
        {
            trit x = (i == 25) ? TRIT_UNKNOWN : TRIT_TRUE;
            v = trit_and(v, x);
        }
        ASSERT(v == TRIT_UNKNOWN,
               "50-deep AND with UNKNOWN at 25 must yield UNKNOWN");
    }
    PASS();
}

/* ── Section F: binary-shaped input {FALSE,TRUE} — check no binary collapse ─ */
static void section_f_binary_input_shape(void)
{
    SECTION("F: binary-shaped inputs {F,T} must NOT collapse to {0,1} outputs");

    TEST("test_6275: AND({F,T},{F,T}) outputs include FALSE=-1 (not 0)");
    ASSERT(trit_and(TRIT_FALSE, TRIT_TRUE) == (trit)-1,
           "AND(F,T) output must be -1, not 0");
    PASS();

    TEST("test_6276: NOT(FALSE=-1) == TRUE=+1 (not flipped to 0)");
    ASSERT(trit_not(TRIT_FALSE) == (trit) + 1,
           "NOT(-1) must be +1 in the ternary domain");
    PASS();

    TEST("test_6277: OR({F,F}) == FALSE=-1, proving F preserved");
    ASSERT(trit_or(TRIT_FALSE, TRIT_FALSE) == (trit)-1,
           "OR(F,F) must be -1, not 0");
    PASS();

    TEST("test_6278: IMPLIES(FALSE,FALSE) == TRUE via Kleene implication");
    /* IMPLIES(a,b) = OR(NOT(a),b); IMPLIES(F,F) = OR(T,F) = T */
    ASSERT(trit_implies(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE,
           "IMPLIES(F,F) must be TRUE");
    PASS();

    TEST("test_6279: EQUIV(FALSE,FALSE) == TRUE — self-equivalence of FALSE");
    ASSERT(trit_equiv(TRIT_FALSE, TRIT_FALSE) == TRIT_TRUE,
           "EQUIV(F,F) must be TRUE");
    PASS();

    TEST("test_6280: EQUIV(TRUE,FALSE) == FALSE — not UNKNOWN");
    ASSERT(trit_equiv(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE,
           "EQUIV(T,F) must be FALSE");
    PASS();
}

/* ── Section G: De Morgan's laws under Kleene K₃ ─────────────────────────── */
static void section_g_de_morgan(void)
{
    SECTION("G: De Morgan's laws hold in Kleene K₃");

    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6281: NOT(AND(a,b)) == OR(NOT a, NOT b) for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
        {
            trit lhs = trit_not(trit_and(vals[i], vals[j]));
            trit rhs = trit_or(trit_not(vals[i]), trit_not(vals[j]));
            ASSERT(lhs == rhs, "De Morgan AND→OR violated");
        }
    PASS();

    TEST("test_6282: NOT(OR(a,b)) == AND(NOT a, NOT b) for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
        {
            trit lhs = trit_not(trit_or(vals[i], vals[j]));
            trit rhs = trit_and(trit_not(vals[i]), trit_not(vals[j]));
            ASSERT(lhs == rhs, "De Morgan OR→AND violated");
        }
    PASS();
}

/* ── Section H: packed64 never collapses UNKNOWN to FALSE under NOT ──────── */
static void section_h_packed64_not_unknown(void)
{
    SECTION("H: packed64 NOT preserves UNKNOWN positions");

    TEST("test_6283: NOT(packed64 with UNKNOWN at every position) == all-UNKNOWN");
    {
        uint64_t all_unknown = 0; /* 0x00 per 2-bit pair */
        uint64_t result = trit_not_packed64(all_unknown);
        /* NOT of 0b00 (UNKNOWN) swaps hi and lo → still 0b00 */
        ASSERT(result == 0,
               "NOT of all-UNKNOWN packed64 must remain all-UNKNOWN");
    }
    PASS();

    TEST("test_6284: NOT(packed64 with TRUE at every pos) == all-FALSE");
    {
        uint64_t all_true = 0;
        for (int i = 0; i < 32; i++)
            all_true |= ((uint64_t)0x01 << (i * 2));
        uint64_t result = trit_not_packed64(all_true);
        uint64_t all_false = 0;
        for (int i = 0; i < 32; i++)
            all_false |= ((uint64_t)0x02 << (i * 2));
        ASSERT(result == all_false, "NOT(all-TRUE) must be all-FALSE");
    }
    PASS();

    TEST("test_6285: NOT(NOT(packed64 word)) == identity for all patterns");
    {
        uint64_t word = 0;
        for (int i = 0; i < 32; i++)
        {
            uint64_t p = (uint64_t)((i % 3 == 0) ? 0x02 : (i % 3 == 1) ? 0x00
                                                                       : 0x01);
            word |= (p << (i * 2));
        }
        ASSERT(trit_not_packed64(trit_not_packed64(word)) == word,
               "double NOT of packed64 must be identity");
    }
    PASS();
}

/* ── Section I: trit_is_definite returns 0 for UNKNOWN in all chain contexts ─ */
static void section_i_definite_guard(void)
{
    SECTION("I: trit_is_definite correctly guards against silent UNKNOWN promotion");

    TEST("test_6286: is_definite never returns 1 for UNKNOWN result of AND(U,T)");
    ASSERT(trit_is_definite(trit_and(TRIT_UNKNOWN, TRIT_TRUE)) == 0,
           "AND(U,T)=U must not be definite");
    PASS();

    TEST("test_6287: is_definite returns 1 for definite AND(T,T)=T");
    ASSERT(trit_is_definite(trit_and(TRIT_TRUE, TRIT_TRUE)) == 1,
           "AND(T,T)=T must be definite");
    PASS();

    TEST("test_6288: trit_to_bool_safe(U) == 0 under binary sentinel check");
    ASSERT(trit_to_bool_safe(TRIT_UNKNOWN) == 0,
           "safe collapse of UNKNOWN must be 0/false");
    PASS();

    TEST("test_6289: trit_to_bool_safe(TRUE) == 1 under binary sentinel check");
    ASSERT(trit_to_bool_safe(TRIT_TRUE) == 1,
           "safe collapse of TRUE must be 1/true");
    PASS();

    TEST("test_6290: trit_to_bool_safe(FALSE) == 0 — FALSE and UNKNOWN both collapse to safe-false");
    ASSERT(trit_to_bool_safe(TRIT_FALSE) == 0,
           "safe collapse of FALSE must be 0");
    PASS();
}

/* ── Section J: commutativity and associativity exhaustive ───────────────── */
static void section_j_commutativity(void)
{
    SECTION("J: commutativity and associativity of AND/OR");

    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6291: AND commutativity: AND(a,b)==AND(b,a) for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ASSERT(trit_and(vals[i], vals[j]) == trit_and(vals[j], vals[i]),
                   "AND must be commutative");
    PASS();

    TEST("test_6292: OR commutativity: OR(a,b)==OR(b,a) for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ASSERT(trit_or(vals[i], vals[j]) == trit_or(vals[j], vals[i]),
                   "OR must be commutative");
    PASS();

    TEST("test_6293: AND associativity: AND(a,AND(b,c))==AND(AND(a,b),c) for all 27 triples");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            for (int k = 0; k < 3; k++)
                ASSERT(trit_and(vals[i], trit_and(vals[j], vals[k])) ==
                           trit_and(trit_and(vals[i], vals[j]), vals[k]),
                       "AND must be associative");
    PASS();

    TEST("test_6294: OR associativity: OR(a,OR(b,c))==OR(OR(a,b),c) for all 27 triples");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            for (int k = 0; k < 3; k++)
                ASSERT(trit_or(vals[i], trit_or(vals[j], vals[k])) ==
                           trit_or(trit_or(vals[i], vals[j]), vals[k]),
                       "OR must be associative");
    PASS();

    TEST("test_6295: distributivity AND over OR: AND(a,OR(b,c))==OR(AND(a,b),AND(a,c))");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            for (int k = 0; k < 3; k++)
            {
                trit lhs = trit_and(vals[i], trit_or(vals[j], vals[k]));
                trit rhs = trit_or(trit_and(vals[i], vals[j]),
                                   trit_and(vals[i], vals[k]));
                ASSERT(lhs == rhs, "AND must distribute over OR");
            }
    PASS();

    TEST("test_6296: distributivity OR over AND: OR(a,AND(b,c))==AND(OR(a,b),OR(a,c))");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            for (int k = 0; k < 3; k++)
            {
                trit lhs = trit_or(vals[i], trit_and(vals[j], vals[k]));
                trit rhs = trit_and(trit_or(vals[i], vals[j]),
                                    trit_or(vals[i], vals[k]));
                ASSERT(lhs == rhs, "OR must distribute over AND");
            }
    PASS();
}

/* ── Section K: idempotency ──────────────────────────────────────────────── */
static void section_k_idempotency(void)
{
    SECTION("K: idempotency AND(a,a)==a and OR(a,a)==a");

    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6297: AND(a,a)==a for all 3 values");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_and(vals[i], vals[i]) == vals[i], "AND must be idempotent");
    PASS();

    TEST("test_6298: OR(a,a)==a for all 3 values");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_or(vals[i], vals[i]) == vals[i], "OR must be idempotent");
    PASS();

    TEST("test_6299: AND chain of 100 TRUE values == TRUE (extreme idempotency)");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 99; i++)
            v = trit_and(v, TRIT_TRUE);
        ASSERT(v == TRIT_TRUE, "AND idempotency must hold for 100 TRUEs");
    }
    PASS();

    TEST("test_6300: OR chain of 100 FALSE values == FALSE (extreme idempotency)");
    {
        trit v = TRIT_FALSE;
        for (int i = 0; i < 99; i++)
            v = trit_or(v, TRIT_FALSE);
        ASSERT(v == TRIT_FALSE, "OR idempotency must hold for 100 FALSEs");
    }
    PASS();

    TEST("test_6301: full binary-reversion guard: outputs cover all {-1,0,+1} across 27 combos");
    {
        int seen_false = 0, seen_unknown = 0, seen_true = 0;
        trit vals3[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
            {
                trit r = trit_and(vals3[i], vals3[j]);
                if (r == TRIT_FALSE)
                    seen_false = 1;
                if (r == TRIT_UNKNOWN)
                    seen_unknown = 1;
                if (r == TRIT_TRUE)
                    seen_true = 1;
            }
        ASSERT(seen_false && seen_unknown && seen_true,
               "AND must produce all three trit values across 9 input combos");
    }
    PASS();
}

/* ── main ────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 90: Red-Team Binary Reversion Attack (Tests 6252-6301) ===\n");

    section_a_not_ternary();
    section_b_and_distinguishes();
    section_c_or_distinguishes();
    section_d_excluded_middle();
    section_e_unknown_propagation();
    section_f_binary_input_shape();
    section_g_de_morgan();
    section_h_packed64_not_unknown();
    section_i_definite_guard();
    section_j_commutativity();
    section_k_idempotency();

    printf("\n--- Results: %d/%d passed", pass_count, test_count);
    if (fail_count)
        printf(", %d FAILED", fail_count);
    printf(" ---\n");

    if (fail_count == 0 && pass_count == test_count)
    {
        printf("Sigma 9: ALL PASS\n");
        return 0;
    }
    printf("SIGMA 9 VIOLATION: %d failure(s)\n", fail_count);
    return 1;
}
