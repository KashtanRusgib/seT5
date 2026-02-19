/*==============================================================================
 * Red-Team Suite 89: Trit Range Integrity
 *
 * Attack surface: adversarial integer inputs, fault-bit patterns, boundary
 * casts, and arithmetic that could produce values outside {-1, 0, +1}.
 *
 * Every trit operation must ALWAYS emit a value that satisfies TRIT_RANGE_CHECK.
 * No path through the ternary stack should silently produce 2, -2, 127, etc.
 *
 * Tests 6202–6251 (50 assertions)
 * Target: 100 % pass (Sigma 9)
 *============================================================================*/

#include <stdio.h>
#include <stdint.h>
#include <string.h>
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

/* ── helpers ─────────────────────────────────────────────────────────────── */
#define IN_RANGE(v) TRIT_RANGE_CHECK(v)

/* Clamp an arbitrary int to the nearest trit — this is the safe bridge */
static inline trit trit_clamp(int v)
{
    if (v > 0)
        return TRIT_TRUE;
    if (v < 0)
        return TRIT_FALSE;
    return TRIT_UNKNOWN;
}

/* ── Section A: TRIT_RANGE_CHECK macro ──────────────────────────────────── */
static void section_a_range_check_macro(void)
{
    SECTION("A: TRIT_RANGE_CHECK macro behaviour");

    TEST("test_6202: TRIT_RANGE_CHECK(TRIT_FALSE=-1) is true");
    ASSERT(TRIT_RANGE_CHECK(TRIT_FALSE), "False=-1 must be in range");
    PASS();

    TEST("test_6203: TRIT_RANGE_CHECK(TRIT_UNKNOWN=0) is true");
    ASSERT(TRIT_RANGE_CHECK(TRIT_UNKNOWN), "Unknown=0 must be in range");
    PASS();

    TEST("test_6204: TRIT_RANGE_CHECK(TRIT_TRUE=+1) is true");
    ASSERT(TRIT_RANGE_CHECK(TRIT_TRUE), "True=+1 must be in range");
    PASS();

    TEST("test_6205: TRIT_RANGE_CHECK(2) is false — attack: int 2 is not a trit");
    ASSERT(!TRIT_RANGE_CHECK(2), "2 out of range, must fail check");
    PASS();

    TEST("test_6206: TRIT_RANGE_CHECK(-2) is false — attack: int -2 is not a trit");
    ASSERT(!TRIT_RANGE_CHECK(-2), "-2 out of range, must fail check");
    PASS();

    TEST("test_6207: TRIT_RANGE_CHECK(127) is false — int8 max attack");
    ASSERT(!TRIT_RANGE_CHECK(127), "INT8_MAX must fail range check");
    PASS();

    TEST("test_6208: TRIT_RANGE_CHECK(-128) is false — int8 min attack");
    ASSERT(!TRIT_RANGE_CHECK(-128), "INT8_MIN must fail range check");
    PASS();
}

/* ── Section B: trit_pack / trit_unpack round-trip ──────────────────────── */
static void section_b_pack_unpack(void)
{
    SECTION("B: trit_pack / trit_unpack round-trips");

    TEST("test_6209: pack(TRIT_FALSE) unpack → TRIT_FALSE");
    ASSERT(trit_unpack(trit_pack(TRIT_FALSE)) == TRIT_FALSE,
           "round-trip FALSE must hold");
    PASS();

    TEST("test_6210: pack(TRIT_UNKNOWN) unpack → TRIT_UNKNOWN");
    ASSERT(trit_unpack(trit_pack(TRIT_UNKNOWN)) == TRIT_UNKNOWN,
           "round-trip UNKNOWN must hold");
    PASS();

    TEST("test_6211: pack(TRIT_TRUE) unpack → TRIT_TRUE");
    ASSERT(trit_unpack(trit_pack(TRIT_TRUE)) == TRIT_TRUE,
           "round-trip TRUE must hold");
    PASS();

    TEST("test_6212: trit_pack(TRIT_FALSE)==0x02 — encoding 10 (neg flag)");
    ASSERT(trit_pack(TRIT_FALSE) == 0x02, "FALSE must encode as 0b10");
    PASS();

    TEST("test_6213: trit_pack(TRIT_UNKNOWN)==0x00 — encoding 00");
    ASSERT(trit_pack(TRIT_UNKNOWN) == 0x00, "UNKNOWN must encode as 0b00");
    PASS();

    TEST("test_6214: trit_pack(TRIT_TRUE)==0x01 — encoding 01 (pos flag)");
    ASSERT(trit_pack(TRIT_TRUE) == 0x01, "TRUE must encode as 0b01");
    PASS();

    TEST("test_6215: trit_unpack(0x03) — fault encoding returns UNKNOWN (clamp)");
    ASSERT(trit_unpack(0x03) == TRIT_UNKNOWN,
           "fault encoding 0b11 must clamp to UNKNOWN");
    PASS();

    TEST("test_6216: trit_unpack result always in range for all 4 patterns");
    for (int p = 0; p < 4; p++)
    {
        ASSERT(IN_RANGE(trit_unpack((trit_packed)p)),
               "all 2-bit patterns must unpack to a valid trit");
    }
    PASS();
}

/* ── Section C: Kleene operator output range ─────────────────────────────── */
static void section_c_kleene_range(void)
{
    SECTION("C: Kleene AND/OR/NOT output always in range");

    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6217: trit_and outputs always in range for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ASSERT(IN_RANGE(trit_and(vals[i], vals[j])),
                   "trit_and output out of range");
    PASS();

    TEST("test_6218: trit_or outputs always in range for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ASSERT(IN_RANGE(trit_or(vals[i], vals[j])),
                   "trit_or output out of range");
    PASS();

    TEST("test_6219: trit_not outputs always in range for all 3 inputs");
    for (int i = 0; i < 3; i++)
        ASSERT(IN_RANGE(trit_not(vals[i])),
               "trit_not output out of range");
    PASS();

    TEST("test_6220: trit_implies outputs always in range for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ASSERT(IN_RANGE(trit_implies(vals[i], vals[j])),
                   "trit_implies out of range");
    PASS();

    TEST("test_6221: trit_equiv outputs always in range for all 9 pairs");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            ASSERT(IN_RANGE(trit_equiv(vals[i], vals[j])),
                   "trit_equiv out of range");
    PASS();
}

/* ── Section D: adversarial clamp bridge ─────────────────────────────────── */
static void section_d_clamp_bridge(void)
{
    SECTION("D: trit_clamp adversarial input bridge");

    TEST("test_6222: clamp(INT8_MAX=127) → TRIT_TRUE, in range");
    ASSERT(trit_clamp(127) == TRIT_TRUE && IN_RANGE(trit_clamp(127)),
           "clamp(127) must be TRUE and in range");
    PASS();

    TEST("test_6223: clamp(INT8_MIN=-128) → TRIT_FALSE, in range");
    ASSERT(trit_clamp(-128) == TRIT_FALSE && IN_RANGE(trit_clamp(-128)),
           "clamp(-128) must be FALSE and in range");
    PASS();

    TEST("test_6224: clamp(0) → TRIT_UNKNOWN, in range");
    ASSERT(trit_clamp(0) == TRIT_UNKNOWN && IN_RANGE(trit_clamp(0)),
           "clamp(0) must be UNKNOWN and in range");
    PASS();

    TEST("test_6225: clamp(INT32_MAX) → TRIT_TRUE, in range");
    ASSERT(trit_clamp(2147483647) == TRIT_TRUE,
           "clamp(INT32_MAX) must be TRUE");
    PASS();

    TEST("test_6226: clamp(INT32_MIN) → TRIT_FALSE, in range");
    ASSERT(trit_clamp((int)-2147483648) == TRIT_FALSE,
           "clamp(INT32_MIN) must be FALSE");
    PASS();

    TEST("test_6227: clamp of trit values are idempotent");
    ASSERT(trit_clamp(TRIT_FALSE) == TRIT_FALSE, "clamp idempotent FALSE");
    ASSERT(trit_clamp(TRIT_UNKNOWN) == TRIT_UNKNOWN, "clamp idempotent UNKNOWN");
    ASSERT(trit_clamp(TRIT_TRUE) == TRIT_TRUE, "clamp idempotent TRUE");
    PASS();
}

/* ── Section E: double / triple NOT stability ────────────────────────────── */
static void section_e_not_stability(void)
{
    SECTION("E: NOT application stability (double-NOT = identity)");

    TEST("test_6228: NOT(NOT(FALSE)) == FALSE (double negation)");
    ASSERT(trit_not(trit_not(TRIT_FALSE)) == TRIT_FALSE,
           "double NOT of FALSE must be FALSE");
    PASS();

    TEST("test_6229: NOT(NOT(UNKNOWN)) == UNKNOWN (double negation)");
    ASSERT(trit_not(trit_not(TRIT_UNKNOWN)) == TRIT_UNKNOWN,
           "double NOT of UNKNOWN must be UNKNOWN");
    PASS();

    TEST("test_6230: NOT(NOT(TRUE)) == TRUE (double negation)");
    ASSERT(trit_not(trit_not(TRIT_TRUE)) == TRIT_TRUE,
           "double NOT of TRUE must be TRUE");
    PASS();

    TEST("test_6231: triple NOT(NOT(NOT(x))) == NOT(x) for all 3 values");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
        {
            trit v3 = trit_not(trit_not(trit_not(vals[i])));
            ASSERT(v3 == trit_not(vals[i]), "triple NOT must equal single NOT");
        }
    }
    PASS();

    TEST("test_6232: 100-chain NOT applied to TRUE: even → TRUE, odd → FALSE");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 100; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_TRUE, "100 NOTs (even) applied to TRUE must yield TRUE");
    }
    PASS();

    TEST("test_6233: 101-chain NOT applied to TRUE: 101 is odd → FALSE");
    {
        trit v = TRIT_TRUE;
        for (int i = 0; i < 101; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_FALSE, "101 NOTs (odd) applied to TRUE must yield FALSE");
    }
    PASS();

    TEST("test_6234: 1000-chain NOT on UNKNOWN always stays UNKNOWN");
    {
        trit v = TRIT_UNKNOWN;
        for (int i = 0; i < 1000; i++)
            v = trit_not(v);
        ASSERT(v == TRIT_UNKNOWN, "NOT chain on UNKNOWN must stay UNKNOWN");
    }
    PASS();
}

/* ── Section F: packed64 output range (every extracted trit in range) ────── */
static void section_f_packed64_output_range(void)
{
    SECTION("F: packed64 extraction always in range");

    /* Build packed word: position i gets trit value (i%3 - 1) */
    uint64_t word = 0;
    for (int i = 0; i < 32; i++)
    {
        trit t = (trit)((i % 3) - 1);
        uint64_t bits = (uint64_t)trit_pack(t);
        word |= (bits << (i * 2));
    }

    TEST("test_6235: all 32 trits extracted from packed64 are in range");
    for (int i = 0; i < 32; i++)
    {
        trit_packed p = (trit_packed)((word >> (i * 2)) & 0x03);
        trit t = trit_unpack(p);
        ASSERT(IN_RANGE(t), "packed64-extracted trit out of range");
    }
    PASS();

    TEST("test_6236: AND of two all-FALSE packed64 words extracts all FALSE");
    {
        uint64_t all_false = 0;
        for (int i = 0; i < 32; i++)
            all_false |= ((uint64_t)0x02 << (i * 2));
        uint64_t result = trit_and_packed64(all_false, all_false);
        for (int i = 0; i < 32; i++)
        {
            trit t = trit_unpack((trit_packed)((result >> (i * 2)) & 0x03));
            ASSERT(t == TRIT_FALSE, "AND of all-false must be all-false");
        }
    }
    PASS();

    TEST("test_6237: OR of two all-TRUE packed64 words extracts all TRUE");
    {
        uint64_t all_true = 0;
        for (int i = 0; i < 32; i++)
            all_true |= ((uint64_t)0x01 << (i * 2));
        uint64_t result = trit_or_packed64(all_true, all_true);
        for (int i = 0; i < 32; i++)
        {
            trit t = trit_unpack((trit_packed)((result >> (i * 2)) & 0x03));
            ASSERT(t == TRIT_TRUE, "OR of all-true must be all-true");
        }
    }
    PASS();
}

/* ── Section G: RUNTIME_VALIDATE passes ─────────────────────────────────── */
static void section_g_runtime_validate(void)
{
    SECTION("G: TRIT_RUNTIME_VALIDATE passes");

    TEST("test_6238: TRIT_RUNTIME_VALIDATE() returns 0 (no deviations)");
    ASSERT(TRIT_RUNTIME_VALIDATE() == 0, "runtime validation failed");
    PASS();

    TEST("test_6239: Kleene AND(U,T) == UNKNOWN — spot check");
    ASSERT(trit_and(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN,
           "AND(U,T) must be UNKNOWN");
    PASS();

    TEST("test_6240: Kleene OR(U,F) == UNKNOWN — spot check");
    ASSERT(trit_or(TRIT_UNKNOWN, TRIT_FALSE) == TRIT_UNKNOWN,
           "OR(U,F) must be UNKNOWN");
    PASS();

    TEST("test_6241: Kleene NOT(UNKNOWN) == UNKNOWN — spot check");
    ASSERT(trit_not(TRIT_UNKNOWN) == TRIT_UNKNOWN,
           "NOT(U) must be UNKNOWN");
    PASS();
}

/* ── Section H: absorptive properties of FALSE and TRUE ──────────────────── */
static void section_h_absorptive(void)
{
    SECTION("H: AND(F,x)=F and OR(T,x)=T for all x (absorptive extremes)");

    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6242: AND(FALSE, x) == FALSE for all x");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_and(TRIT_FALSE, vals[i]) == TRIT_FALSE,
               "AND(F,x) must be F");
    PASS();

    TEST("test_6243: AND(x, FALSE) == FALSE for all x (commutativity)");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_and(vals[i], TRIT_FALSE) == TRIT_FALSE,
               "AND(x,F) must be F");
    PASS();

    TEST("test_6244: OR(TRUE, x) == TRUE for all x");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_or(TRIT_TRUE, vals[i]) == TRIT_TRUE,
               "OR(T,x) must be T");
    PASS();

    TEST("test_6245: OR(x, TRUE) == TRUE for all x (commutativity)");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_or(vals[i], TRIT_TRUE) == TRIT_TRUE,
               "OR(x,T) must be T");
    PASS();

    TEST("test_6246: AND(TRUE, x) == x for all x (identity)");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_and(TRIT_TRUE, vals[i]) == vals[i],
               "AND(T,x) must be x");
    PASS();

    TEST("test_6247: OR(FALSE, x) == x for all x (identity)");
    for (int i = 0; i < 3; i++)
        ASSERT(trit_or(TRIT_FALSE, vals[i]) == vals[i],
               "OR(F,x) must be x");
    PASS();
}

/* ── Section I: trit_is_definite and trit_to_bool_safe ───────────────────── */
static void section_i_predicates(void)
{
    SECTION("I: trit predicates under adversarial use");

    TEST("test_6248: trit_is_definite(UNKNOWN) == 0 (not definite)");
    ASSERT(trit_is_definite(TRIT_UNKNOWN) == 0,
           "UNKNOWN is not definite");
    PASS();

    TEST("test_6249: trit_is_definite(TRUE) == 1 (definite)");
    ASSERT(trit_is_definite(TRIT_TRUE) == 1, "TRUE is definite");
    PASS();

    TEST("test_6250: trit_to_bool_safe(UNKNOWN) == 0 (conservative collapse)");
    ASSERT(trit_to_bool_safe(TRIT_UNKNOWN) == 0,
           "UNKNOWN conservatively collapses to false");
    PASS();

    TEST("test_6251: trit_to_bool_safe(FALSE) == 0 (safe collapse)");
    ASSERT(trit_to_bool_safe(TRIT_FALSE) == 0,
           "FALSE collapses to false");
    PASS();
}

/* ── main ────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 89: Red-Team Trit Range Integrity (Tests 6202-6251) ===\n");

    section_a_range_check_macro();
    section_b_pack_unpack();
    section_c_kleene_range();
    section_d_clamp_bridge();
    section_e_not_stability();
    section_f_packed64_output_range();
    section_g_runtime_validate();
    section_h_absorptive();
    section_i_predicates();

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
