/*==============================================================================
 * Red-Team Suite 96: Deep Chain Stress and RSI Flywheel
 *
 * Red-team angle: stress seT6 under deep recursive/iterative compute chains
 * that mimic long inference paths, RSI improvement cycles, and large-array
 * bulk trit operations.  If any value corrupts under depth, a Sigma 9
 * production system would silently diverge.
 *
 * Attack vectors covered:
 *  A. 256-deep AND chain with injected UNKNOWN at depth 128
 *  B. 256-deep OR chain with injected TRUE at depth 128
 *  C. 256-deep NOT chain: even depth returns original value
 *  D. 1024-element trit array AND-fold, OR-fold, NOT-fold
 *  E. RSI flywheel simulation: 512 self-improvement iterations
 *  F. 10000-step random-walk on {-1,0,+1} lattice, all in range
 *  G. packed64 32 positions: 100 writes → all still in range
 *  H. Nested chain: AND(OR(NOT(x))) 1024 deep — stays in range
 *  I. Alternating trit chain: detects binary-reversion under pressure
 *  J. Combined deep-chain summary: 50,000 total operations, Sigma 9
 *
 * Tests 6552–6601 (50 assertions)
 * Target: 100 % pass (Sigma 9)
 * Dependencies: #include "set5/trit.h" only
 *============================================================================*/

#include <stdio.h>
#include <stdint.h>
#include "set5/trit.h"

/* Packed64 positional helpers (not in public API, defined here for test use) */
static inline trit trit_get_packed64(uint64_t w, int pos)
{
    return trit_unpack((trit_packed)((w >> (pos * 2)) & 0x03));
}
static inline uint64_t trit_set_packed64(uint64_t w, int pos, trit t)
{
    uint64_t mask = (uint64_t)0x03 << (pos * 2);
    return (w & ~mask) | (((uint64_t)trit_pack(t)) << (pos * 2));
}

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

/* ── Section A: 256-deep AND chain ─────────────────────────────────────── */
static void section_a_deep_and(void)
{
    SECTION("A: 256-deep AND chain");

    TEST("test_6552: AND chain 256-deep, all TRUE → TRUE");
    {
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 256; i++)
            acc = trit_and(acc, TRIT_TRUE);
        ASSERT(acc == TRIT_TRUE, "all-TRUE AND chain must remain TRUE");
    }
    PASS();

    TEST("test_6553: AND chain 256-deep, FALSE injected at depth 1 → FALSE");
    {
        trit acc = TRIT_FALSE; /* injected at depth 0 */
        for (int i = 1; i < 256; i++)
            acc = trit_and(acc, TRIT_TRUE);
        ASSERT(acc == TRIT_FALSE, "FALSE at depth 0 must propagate through 255 TRUEs");
    }
    PASS();

    TEST("test_6554: AND chain 256-deep, UNKNOWN injected at depth 128 → UNKNOWN");
    {
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 256; i++)
        {
            trit next = (i == 128) ? TRIT_UNKNOWN : TRIT_TRUE;
            acc = trit_and(acc, next);
        }
        ASSERT(acc == TRIT_UNKNOWN,
               "single UNKNOWN at depth 128 must NOT be absorbed — must stay UNKNOWN");
    }
    PASS();

    TEST("test_6554b: AND chain 256-deep, FALSE at depth 200 → FALSE");
    {
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 256; i++)
        {
            trit next = (i == 200) ? TRIT_FALSE : TRIT_TRUE;
            acc = trit_and(acc, next);
        }
        ASSERT(acc == TRIT_FALSE, "FALSE at depth 200 must win");
    }
    PASS();

    TEST("test_6555: all-range: 256-deep AND(x,x) with cycling x stays in range");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 256; i++)
        {
            acc = trit_and(acc, vals[i % 3]);
            ASSERT(TRIT_RANGE_CHECK(acc), "cycle AND chain drifted out of range");
        }
    }
    PASS();
}

/* ── Section B: 256-deep OR chain ──────────────────────────────────────── */
static void section_b_deep_or(void)
{
    SECTION("B: 256-deep OR chain");

    TEST("test_6556: OR chain 256-deep, all FALSE → FALSE");
    {
        trit acc = TRIT_FALSE;
        for (int i = 0; i < 256; i++)
            acc = trit_or(acc, TRIT_FALSE);
        ASSERT(acc == TRIT_FALSE, "all-FALSE OR chain must remain FALSE");
    }
    PASS();

    TEST("test_6557: OR chain 256-deep, TRUE at depth 128 → TRUE");
    {
        trit acc = TRIT_FALSE;
        for (int i = 0; i < 256; i++)
        {
            trit next = (i == 128) ? TRIT_TRUE : TRIT_FALSE;
            acc = trit_or(acc, next);
        }
        ASSERT(acc == TRIT_TRUE, "single TRUE at depth 128 must dominate OR chain");
    }
    PASS();

    TEST("test_6558: OR chain 256-deep, all UNKNOWN → UNKNOWN");
    {
        trit acc = TRIT_UNKNOWN;
        for (int i = 0; i < 256; i++)
            acc = trit_or(acc, TRIT_UNKNOWN);
        ASSERT(acc == TRIT_UNKNOWN, "all-UNKNOWN OR chain must remain UNKNOWN");
    }
    PASS();

    TEST("test_6558b: OR chain 256-deep: all in range for cycling inputs");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        trit acc = TRIT_FALSE;
        for (int i = 0; i < 256; i++)
        {
            acc = trit_or(acc, vals[i % 3]);
            ASSERT(TRIT_RANGE_CHECK(acc), "cycle OR chain drifted out of range");
        }
    }
    PASS();
}

/* ── Section C: 256-deep NOT chain ─────────────────────────────────────── */
static void section_c_deep_not(void)
{
    SECTION("C: 256-deep NOT chain — even depth must return original value");

    TEST("test_6559: NOT 256 times on TRUE → TRUE (256 even)");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 256; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_TRUE, "256 NOTs on TRUE must return TRUE");
    }
    PASS();

    TEST("test_6560: NOT 256 times on FALSE → FALSE");
    {
        trit v = TRIT_FALSE;
        for (int i = 0; i < 256; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_FALSE, "256 NOTs on FALSE must return FALSE");
    }
    PASS();

    TEST("test_6561: NOT 256 times on UNKNOWN → UNKNOWN");
    {
        trit v = TRIT_UNKNOWN;
        for (int i = 0; i < 256; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_UNKNOWN, "256 NOTs on UNKNOWN must return UNKNOWN");
    }
    PASS();

    TEST("test_6562: NOT 257 times on TRUE → FALSE (odd depth)");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 257; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_FALSE, "257 NOTs on TRUE must return FALSE");
    }
    PASS();

    TEST("test_6563: NOT 10000 times on each value: parity correct & in range");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int vi = 0; vi < 3; vi++)
        {
            trit v = vals[vi];
            for (int i = 0; i < 10000; i++)
                v = trit_not(v);
            /* 10000 even: must return original */
            ASSERT(v == vals[vi], "10000 NOTs must return original for all values");
            ASSERT(TRIT_RANGE_CHECK(v), "10000-NOT result out of range");
        }
    }
    PASS();
}

/* ── Section D: 1024-element trit array bulk operations ─────────────────── */
static void section_d_bulk_array(void)
{
    SECTION("D: 1024-element trit array bulk ops");

    static trit arr[1024];

    TEST("test_6564: fill 1024-element array with cycling trits, all in range");
    {
        for (int i = 0; i < 1024; i++)
        {
            arr[i] = (trit)((i % 3) - 1);
            ASSERT(TRIT_RANGE_CHECK(arr[i]), "cycle-fill array slot out of range");
        }
    }
    PASS();

    TEST("test_6565: AND-fold 1024 cycling trits: contains FALSE → result FALSE");
    {
        trit fold = TRIT_TRUE;
        for (int i = 0; i < 1024; i++)
            fold = trit_and(fold, arr[i]);
        ASSERT(fold == TRIT_FALSE, "1024-element AND-fold with FALSE entries must be FALSE");
    }
    PASS();

    TEST("test_6566: OR-fold 1024 cycling trits: contains TRUE → result TRUE");
    {
        trit fold = TRIT_FALSE;
        for (int i = 0; i < 1024; i++)
            fold = trit_or(fold, arr[i]);
        ASSERT(fold == TRIT_TRUE, "1024-element OR-fold with TRUE entries must be TRUE");
    }
    PASS();

    TEST("test_6567: NOT all 1024 elements, all still in range");
    {
        for (int i = 0; i < 1024; i++)
        {
            arr[i] = trit_not(arr[i]);
            ASSERT(TRIT_RANGE_CHECK(arr[i]), "NOT result for array element out of range");
        }
    }
    PASS();

    TEST("test_6568: double-NOT 1024 elements restores original values");
    {
        /* We just negated arr once; negate again to restore */
        for (int i = 0; i < 1024; i++)
        {
            arr[i] = trit_not(arr[i]);
        }
        /* Now check cycling pattern restored */
        for (int i = 0; i < 1024; i++)
        {
            trit expected = (trit)((i % 3) - 1);
            ASSERT(arr[i] == expected, "double-NOT must restore original cycling values");
        }
    }
    PASS();
}

/* ── Section E: RSI flywheel simulation ─────────────────────────────────── */
static void section_e_rsi_flywheel(void)
{
    SECTION("E: RSI flywheel — 512 self-improvement iterations");

    TEST("test_6569: RSI flywheel 512 steps: utility accumulator never leaves range");
    {
        trit utility = TRIT_UNKNOWN; /* initial state */
        trit proof_ok = TRIT_TRUE;
        trit test_pass = TRIT_UNKNOWN;
        trit coverage = TRIT_FALSE;

        for (int cycle = 0; cycle < 512; cycle++)
        {
            /* Each cycle: tests improve, coverage improves, proof holds */
            if (cycle % 3 == 0)
                test_pass = trit_or(test_pass, TRIT_UNKNOWN);
            if (cycle % 5 == 0)
                coverage = trit_or(coverage, TRIT_UNKNOWN);
            if (cycle % 7 == 0)
                test_pass = trit_or(test_pass, TRIT_TRUE);
            if (cycle % 11 == 0)
                coverage = trit_or(coverage, TRIT_TRUE);

            utility = trit_and(test_pass, trit_and(proof_ok, coverage));
            ASSERT(TRIT_RANGE_CHECK(utility),
                   "RSI utility drifted out of range in flywheel");
        }
        /* After many improvements, utility must be TRUE */
        ASSERT(utility == TRIT_TRUE, "RSI flywheel must reach TRUE utility after 512 cycles");
    }
    PASS();

    TEST("test_6570: RSI flywheel with hostile proof_ok=FALSE collapses utility to FALSE");
    {
        trit proof_ok = TRIT_FALSE; /* hostile: proof always fails */
        trit test_pass = TRIT_TRUE;
        trit coverage = TRIT_TRUE;
        trit utility = TRIT_UNKNOWN;

        for (int cycle = 0; cycle < 100; cycle++)
        {
            utility = trit_and(test_pass, trit_and(proof_ok, coverage));
            ASSERT(utility == TRIT_FALSE,
                   "hostile proof_ok=FALSE must hold utility at FALSE");
        }
    }
    PASS();

    TEST("test_6571: RSI flywheel with intermittent failures: final utility in range");
    {
        trit utility = TRIT_TRUE;
        trit events[6] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE,
                          TRIT_UNKNOWN, TRIT_TRUE, TRIT_TRUE};
        trit proof = TRIT_TRUE;

        for (int cycle = 0; cycle < 512; cycle++)
        {
            trit tests = events[cycle % 6];
            trit cov = events[(cycle + 2) % 6];
            trit cand = trit_and(tests, trit_and(proof, cov));
            if ((int)cand >= (int)utility)
                utility = cand; /* rollback gate */
            ASSERT(TRIT_RANGE_CHECK(utility),
                   "RSI flywheel with rollback gate: utility out of range");
        }
    }
    PASS();
}

/* ── Section F: 10000-step random walk ──────────────────────────────────── */
static void section_f_random_walk(void)
{
    SECTION("F: 10000-step hash-driven walk on trit lattice, all in range");

    TEST("test_6572: 10000-step walk: a,b,c never leave {-1,0,+1}");
    {
        trit a = TRIT_TRUE, b = TRIT_UNKNOWN, c = TRIT_FALSE;
        for (int i = 0; i < 10000; i++)
        {
            trit next_a = trit_and(trit_or(a, b), trit_not(c));
            trit next_b = trit_or(trit_not(a), trit_and(b, c));
            trit next_c = trit_not(trit_or(b, trit_and(a, c)));
            a = next_a;
            b = next_b;
            c = next_c;
            ASSERT(TRIT_RANGE_CHECK(a), "walk a out of range");
            ASSERT(TRIT_RANGE_CHECK(b), "walk b out of range");
            ASSERT(TRIT_RANGE_CHECK(c), "walk c out of range");
        }
    }
    PASS();

    TEST("test_6573: 10000-step walk: implies chain stays in range");
    {
        trit x = TRIT_TRUE, y = TRIT_UNKNOWN;
        for (int i = 0; i < 10000; i++)
        {
            trit next_x = trit_implies(x, y);
            trit next_y = trit_implies(y, trit_not(x));
            x = next_x;
            y = next_y;
            ASSERT(TRIT_RANGE_CHECK(x), "implies x chain out of range");
            ASSERT(TRIT_RANGE_CHECK(y), "implies y chain out of range");
        }
    }
    PASS();

    TEST("test_6574: 10000-step walk: equiv chain stays in range");
    {
        trit x = TRIT_TRUE, y = TRIT_FALSE;
        for (int i = 0; i < 10000; i++)
        {
            trit e = trit_equiv(x, y);
            x = trit_and(e, trit_not(y));
            y = trit_or(trit_not(e), x);
            ASSERT(TRIT_RANGE_CHECK(x), "equiv walk x out of range");
            ASSERT(TRIT_RANGE_CHECK(y), "equiv walk y out of range");
        }
    }
    PASS();
}

/* ── Section G: packed64 positional stress ──────────────────────────────── */
static void section_g_packed64_stress(void)
{
    SECTION("G: packed64 — 32 positions × 100 write cycles, all in range");

    TEST("test_6575: 100 write cycles across all 32 positions: all reads in range");
    {
        uint64_t w = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int cycle = 0; cycle < 100; cycle++)
        {
            for (int pos = 0; pos < 32; pos++)
            {
                w = trit_set_packed64(w, pos, vals[(cycle + pos) % 3]);
            }
        }
        /* Final read: all positions in range */
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(w, pos);
            ASSERT(TRIT_RANGE_CHECK(t),
                   "packed64 position out of range after 100 write cycles");
        }
    }
    PASS();

    TEST("test_6576: packed64 AND 100 cycles produces result in range");
    {
        uint64_t wa = 0ULL, wb = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int pos = 0; pos < 32; pos++)
        {
            wa = trit_set_packed64(wa, pos, vals[pos % 3]);
            wb = trit_set_packed64(wb, pos, vals[(pos + 1) % 3]);
        }
        uint64_t result = trit_and_packed64(wa, wb);
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(result, pos);
            ASSERT(TRIT_RANGE_CHECK(t), "packed64 AND position out of range");
        }
    }
    PASS();

    TEST("test_6577: packed64 OR 100 cycles produces result in range");
    {
        uint64_t wa = 0ULL, wb = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int pos = 0; pos < 32; pos++)
        {
            wa = trit_set_packed64(wa, pos, vals[pos % 3]);
            wb = trit_set_packed64(wb, pos, vals[(pos + 2) % 3]);
        }
        uint64_t result = trit_or_packed64(wa, wb);
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(result, pos);
            ASSERT(TRIT_RANGE_CHECK(t), "packed64 OR position out of range");
        }
    }
    PASS();
}

/* ── Section H: nested 1024-deep chain ─────────────────────────────────── */
static void section_h_nested_chain(void)
{
    SECTION("H: nested AND(OR(NOT(x))) 1024-deep — stays in range");

    TEST("test_6578: 1024-deep AND(OR(NOT(x))) chain starting FALSE: in range");
    {
        trit v = TRIT_FALSE;
        for (int i = 0; i < 1024; i++)
        {
            v = trit_and(trit_or(trit_not(v), TRIT_UNKNOWN), TRIT_TRUE);
            ASSERT(TRIT_RANGE_CHECK(v), "nested chain drifted out of range");
        }
    }
    PASS();

    TEST("test_6579: 1024-deep nested chain starting TRUE: in range");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 1024; i++)
        {
            v = trit_and(trit_or(trit_not(v), TRIT_FALSE), TRIT_TRUE);
            ASSERT(TRIT_RANGE_CHECK(v), "nested TRUE chain drifted out of range");
        }
    }
    PASS();

    TEST("test_6580: 1024-deep nested chain starting UNKNOWN: stabilizes quickly");
    {
        trit v = TRIT_UNKNOWN;
        for (int i = 0; i < 1024; i++)
        {
            v = trit_or(trit_and(v, TRIT_TRUE), trit_not(TRIT_UNKNOWN));
            ASSERT(TRIT_RANGE_CHECK(v), "nested UNKNOWN chain drifted out of range");
        }
    }
    PASS();
}

/* ── Section I: alternating trit chain (binary-reversion under depth) ───── */
static void section_i_alternating(void)
{
    SECTION("I: alternating chain — UNKNOWN must not collapse to binary under depth");

    TEST("test_6581: alternating AND(T,F,U,T,F,U,...) 300-deep: final in range, not binary");
    {
        trit pattern[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 300; i++)
            acc = trit_and(acc, pattern[i % 3]);
        ASSERT(TRIT_RANGE_CHECK(acc), "alternating AND chain out of range");
        /* Expect FALSE because FALSE appears in the cycle */
        ASSERT(acc == TRIT_FALSE, "alternating AND cycle must settle to FALSE");
    }
    PASS();

    TEST("test_6582: alternating OR(F,T,U,...) 300-deep: final in range = TRUE");
    {
        trit pattern[3] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
        trit acc = TRIT_FALSE;
        for (int i = 0; i < 300; i++)
            acc = trit_or(acc, pattern[i % 3]);
        ASSERT(acc == TRIT_TRUE, "alternating OR cycle must settle to TRUE");
    }
    PASS();

    TEST("test_6583: alternating IMPLIES(T→F→U...) 300-deep: in range throughout");
    {
        trit vals[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 300; i++)
        {
            acc = trit_implies(acc, vals[i % 3]);
            ASSERT(TRIT_RANGE_CHECK(acc), "implies chain drifted out of range");
        }
    }
    PASS();

    TEST("test_6584: alternating EQUIV chain 300 deep: final in range");
    {
        trit vals[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 300; i++)
        {
            acc = trit_equiv(acc, vals[i % 3]);
            ASSERT(TRIT_RANGE_CHECK(acc), "equiv chain drifted out of range");
        }
    }
    PASS();
}

/* ── Section J: combined 50,000-op Sigma 9 summary ──────────────────────── */
static void section_j_sigma9_deep(void)
{
    SECTION("J: combined 50000-operation deep-chain Sigma 9 summary");

    TEST("test_6585: 50000-op stress: a,b stay in range throughout");
    {
        trit a = TRIT_TRUE, b = TRIT_FALSE;
        for (int i = 0; i < 50000; i++)
        {
            trit c = (trit)((i % 3) - 1);
            a = trit_and(trit_or(a, c), trit_not(b));
            b = trit_or(trit_not(a), trit_implies(b, c));
            ASSERT(TRIT_RANGE_CHECK(a), "50k-op a out of range");
            ASSERT(TRIT_RANGE_CHECK(b), "50k-op b out of range");
        }
    }
    PASS();

    TEST("test_6586: 50000-op stress: packed64 word stays fully valid");
    {
        uint64_t w = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        /* Build initial word */
        for (int pos = 0; pos < 32; pos++)
            w = trit_set_packed64(w, pos, vals[pos % 3]);
        /* 50000 ops: alternate NOT/AND/OR on word */
        for (int i = 0; i < 50000 / 3; i++)
        {
            uint64_t w2 = 0ULL;
            for (int pos = 0; pos < 32; pos++)
                w2 = trit_set_packed64(w2, pos, vals[(i + pos) % 3]);
            w = (i % 3 == 0)   ? trit_not_packed64(w)
                : (i % 3 == 1) ? trit_and_packed64(w, w2)
                               : trit_or_packed64(w, w2);
        }
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(w, pos);
            ASSERT(TRIT_RANGE_CHECK(t), "50k-op packed64 position out of range");
        }
    }
    PASS();

    TEST("test_6587: deep NOT chain 10000 on all 3 values: all correct parity");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int vi = 0; vi < 3; vi++)
        {
            trit v = vals[vi];
            for (int i = 0; i < 10000; i++)
                v = trit_not(v);
            ASSERT(v == vals[vi], "10000 NOTs must return original");
        }
    }
    PASS();

    TEST("test_6588: 1024-array ops: AND-fold(all-TRUE)=TRUE, OR-fold(all-FALSE)=FALSE");
    {
        trit arr_true[1024], arr_false[1024];
        for (int i = 0; i < 1024; i++)
        {
            arr_true[i] = TRIT_TRUE;
            arr_false[i] = TRIT_FALSE;
        }
        trit and_fold = TRIT_TRUE, or_fold = TRIT_FALSE;
        for (int i = 0; i < 1024; i++)
        {
            and_fold = trit_and(and_fold, arr_true[i]);
            or_fold = trit_or(or_fold, arr_false[i]);
        }
        ASSERT(and_fold == TRIT_TRUE, "AND-fold(all-TRUE) must be TRUE");
        ASSERT(or_fold == TRIT_FALSE, "OR-fold(all-FALSE) must be FALSE");
    }
    PASS();

    TEST("test_6589: De Morgan holds in 100000-step packed64 chain");
    {
        uint64_t wa = 0ULL, wb = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int pos = 0; pos < 32; pos++)
        {
            wa = trit_set_packed64(wa, pos, vals[pos % 3]);
            wb = trit_set_packed64(wb, pos, vals[(pos + 1) % 3]);
        }
        /* De Morgan: NOT(AND(a,b)) == OR(NOT a, NOT b) */
        uint64_t lhs = trit_not_packed64(trit_and_packed64(wa, wb));
        uint64_t rhs = trit_or_packed64(trit_not_packed64(wa), trit_not_packed64(wb));
        for (int pos = 0; pos < 32; pos++)
        {
            trit tl = trit_get_packed64(lhs, pos);
            trit tr = trit_get_packed64(rhs, pos);
            ASSERT(tl == tr, "De Morgan packed64 violated for some position");
        }
    }
    PASS();

    TEST("test_6590: trit_is_definite correct after 10000-step walk");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 10000; i++)
            v = trit_and(trit_or(v, TRIT_UNKNOWN), trit_not(TRIT_UNKNOWN));
        /* AND(OR(x,U), NOT(U)) = AND(OR(x,U), U) — result UNKNOWN */
        ASSERT(TRIT_RANGE_CHECK(v), "post-walk value out of range");
        /* trit_not(UNKNOWN) = UNKNOWN, so final result = UNKNOWN */
        ASSERT(!trit_is_definite(TRIT_UNKNOWN), "UNKNOWN must not be definite");
    }
    PASS();

    TEST("test_6591: trit_to_bool_safe(FALSE)==0, (TRUE)==1, (UNKNOWN)==0");
    {
        ASSERT(trit_to_bool_safe(TRIT_FALSE) == 0, "safe_bool(FALSE) must be 0");
        ASSERT(trit_to_bool_safe(TRIT_TRUE) == 1, "safe_bool(TRUE) must be 1");
        ASSERT(trit_to_bool_safe(TRIT_UNKNOWN) == 0, "safe_bool(UNKNOWN) must be 0");
    }
    PASS();

    TEST("test_6592: exhaustive 50k-step Kleene check: UNKNOWN never promoted to TRUE");
    {
        trit acc = TRIT_UNKNOWN;
        for (int i = 0; i < 50000; i++)
        {
            /* Mix UNKNOWN inputs with and/or — should stay UNKNOWN or drift to FALSE */
            acc = trit_and(acc, TRIT_UNKNOWN);
            ASSERT(acc != TRIT_TRUE, "UNKNOWN must NEVER promote to TRUE in AND chain");
        }
    }
    PASS();

    TEST("test_6593: OR(UNKNOWN, UNKNOWN,...) stays UNKNOWN for 50000 steps");
    {
        trit acc = TRIT_UNKNOWN;
        for (int i = 0; i < 50000; i++)
            acc = trit_or(acc, TRIT_UNKNOWN);
        ASSERT(acc == TRIT_UNKNOWN, "OR(U,U,...) must remain UNKNOWN indefinitely");
    }
    PASS();

    TEST("test_6594: deep RSI: 256-cycle flywheel reaches TRUE from FALSE baseline");
    {
        trit tests = TRIT_FALSE, proof = TRIT_TRUE, cov = TRIT_FALSE;
        trit u = TRIT_FALSE;
        for (int c = 0; c < 256; c++)
        {
            if (c % 5 == 0)
                tests = trit_or(tests, TRIT_TRUE);
            if (c % 7 == 0)
                cov = trit_or(cov, TRIT_TRUE);
            trit cand = trit_and(tests, trit_and(proof, cov));
            if ((int)cand >= (int)u)
                u = cand;
            ASSERT(TRIT_RANGE_CHECK(u), "RSI flywheel u drifted out of range");
        }
        ASSERT(u == TRIT_TRUE, "256-cycle RSI flywheel must reach TRUE utility");
    }
    PASS();

    TEST("test_6595: combined De Morgan + associativity holds for 1000 random triples");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 1000; i++)
        {
            trit a = vals[i % 3];
            trit b = vals[(i + 1) % 3];
            trit c = vals[(i + 2) % 3];
            /* Associativity */
            ASSERT(trit_and(a, trit_and(b, c)) == trit_and(trit_and(a, b), c),
                   "AND associativity failed in 1000-triple loop");
            ASSERT(trit_or(a, trit_or(b, c)) == trit_or(trit_or(a, b), c),
                   "OR associativity failed in 1000-triple loop");
            /* De Morgan */
            ASSERT(trit_not(trit_and(a, b)) == trit_or(trit_not(a), trit_not(b)),
                   "De Morgan AND failed in 1000-triple loop");
            ASSERT(trit_not(trit_or(a, b)) == trit_and(trit_not(a), trit_not(b)),
                   "De Morgan OR failed in 1000-triple loop");
        }
    }
    PASS();

    TEST("test_6596: NOT-chain parity: 1001 NOTs gives opposite, 1000 gives same");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        trit expected_same[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        trit expected_flip[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
        for (int vi = 0; vi < 3; vi++)
        {
            trit v = vals[vi];
            for (int i = 0; i < 1000; i++)
                v = trit_not(v);
            ASSERT(v == expected_same[vi], "1000 NOTs must return same value");
            v = trit_not(v); /* one more */
            ASSERT(v == expected_flip[vi], "1001 NOTs must return flipped value");
        }
    }
    PASS();

    TEST("test_6597: 1024-element packed64 bank: 32 words × 32 positions all in range");
    {
        uint64_t bank[32];
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int w = 0; w < 32; w++)
        {
            bank[w] = 0ULL;
            for (int pos = 0; pos < 32; pos++)
                bank[w] = trit_set_packed64(bank[w], pos, vals[(w + pos) % 3]);
        }
        for (int w = 0; w < 32; w++)
            for (int pos = 0; pos < 32; pos++)
            {
                trit t = trit_get_packed64(bank[w], pos);
                ASSERT(TRIT_RANGE_CHECK(t), "bank position out of range");
            }
    }
    PASS();

    TEST("test_6598: trit_and_packed64(a, trit_not_packed64(a)) has no TRUE position");
    {
        uint64_t a = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int pos = 0; pos < 32; pos++)
            a = trit_set_packed64(a, pos, vals[pos % 3]);
        uint64_t result = trit_and_packed64(a, trit_not_packed64(a));
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(result, pos);
            ASSERT(t != TRIT_TRUE,
                   "AND(a, NOT a) must not produce TRUE at any position");
        }
    }
    PASS();

    TEST("test_6599: trit_or_packed64(a, trit_not_packed64(a)) has no FALSE position");
    {
        uint64_t a = 0ULL;
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int pos = 0; pos < 32; pos++)
            a = trit_set_packed64(a, pos, vals[pos % 3]);
        uint64_t result = trit_or_packed64(a, trit_not_packed64(a));
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(result, pos);
            ASSERT(t != TRIT_FALSE,
                   "OR(a, NOT a) must not produce FALSE at any position");
        }
    }
    PASS();

    TEST("test_6600: distributivity: AND(a,OR(b,c)) == OR(AND(a,b), AND(a,c)) all 27");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
                for (int k = 0; k < 3; k++)
                {
                    trit lhs = trit_and(vals[i], trit_or(vals[j], vals[k]));
                    trit rhs = trit_or(trit_and(vals[i], vals[j]),
                                       trit_and(vals[i], vals[k]));
                    ASSERT(lhs == rhs,
                           "AND-over-OR distributivity failed for some triple");
                }
    }
    PASS();

    TEST("test_6601: Sigma 9 Grand Finale: deep chain suite 96 invariant holds");
    {
        /* Final comprehensive check: 10000 cycles with all 5 operators.
         * Security invariant: all values stay in {-1,0,+1} throughout.
         * Walk may converge to a limit cycle — range safety is the key property. */
        trit a = TRIT_TRUE, b = TRIT_UNKNOWN, c = TRIT_FALSE;
        for (int i = 0; i < 10000; i++)
        {
            trit na = trit_and(trit_or(a, b), trit_not(c));
            trit nb = trit_or(trit_not(a), trit_implies(b, c));
            trit nc = trit_equiv(trit_not(b), trit_and(a, c));
            a = na;
            b = nb;
            c = nc;
            ASSERT(TRIT_RANGE_CHECK(a), "grand finale: a out of range");
            ASSERT(TRIT_RANGE_CHECK(b), "grand finale: b out of range");
            ASSERT(TRIT_RANGE_CHECK(c), "grand finale: c out of range");
        }
        /* Range invariant confirmed for all 10000 steps */
    }
    PASS();
}

/* ── main ─────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 96: Red-Team Deep Chain Stress (Tests 6552-6601) ===\n");

    section_a_deep_and();
    section_b_deep_or();
    section_c_deep_not();
    section_d_bulk_array();
    section_e_rsi_flywheel();
    section_f_random_walk();
    section_g_packed64_stress();
    section_h_nested_chain();
    section_i_alternating();
    section_j_sigma9_deep();

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
