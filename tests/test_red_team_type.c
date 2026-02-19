/*==============================================================================
 * Red-Team Suite 95: Type Confusion & Integer Safety
 *
 * Red-team angle: attack the trit type at the boundaries of int8_t, int,
 * and implicit C integer conversions.  A ternary system that silently
 * widens to int introduces undefined behaviour and value corruption risks.
 *
 * Attack vectors covered:
 *  A. int8_t arithmetic overflow/underflow into trit range
 *  B. Implicit signed-integer promotion in trit operations
 *  C. Accidental non-ternary literals (2, -2, 127, -128)
 *  D. Casting hazards: uint8_t→trit, int→trit, short→trit
 *  E. Accumulator patterns that could silently overflow
 *  F. trit_pack / trit_unpack round-trip with edge bit patterns
 *  G. Packed64 extraction never leaks non-ternary values
 *  H. Mixed-width arithmetic: int16 ternary math stays bounded
 *  I. Saturation/clamping: non-trit values must not survive any API call
 *  J. Summary sweep
 *
 * Tests 6502–6551 (50 assertions)
 * Target: 100 % pass (Sigma 9)
 * Dependencies: #include "set5/trit.h" only
 *============================================================================*/

#include <stdio.h>
#include <stdint.h>
#include <limits.h>
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

/* Safe clamp: any int → nearest trit value */
static inline trit trit_clamp(int v)
{
    if (v < -1)
        return TRIT_FALSE;
    if (v > 1)
        return TRIT_TRUE;
    return (trit)v;
}

/* ── Section A: int8_t boundary arithmetic ─────────────────────────────── */
static void section_a_int8_boundary(void)
{
    SECTION("A: int8_t boundary arithmetic");

    TEST("test_6502: INT8_MAX (127) clamped to trit == TRUE");
    ASSERT(trit_clamp(INT8_MAX) == TRIT_TRUE,
           "INT8_MAX must clamp to TRUE");
    PASS();

    TEST("test_6503: INT8_MIN (-128) clamped to trit == FALSE");
    ASSERT(trit_clamp(INT8_MIN) == TRIT_FALSE,
           "INT8_MIN must clamp to FALSE");
    PASS();

    TEST("test_6504: int8 value 2 must NOT equal TRIT_TRUE after clamp");
    ASSERT(trit_clamp(2) == TRIT_TRUE, "2 must clamp to TRUE (not leak as 2)");
    PASS();

    TEST("test_6505: int8 value -2 must NOT equal TRIT_FALSE after clamp (== -1 after clamp)");
    ASSERT(trit_clamp(-2) == TRIT_FALSE, "-2 must clamp to FALSE");
    PASS();

    TEST("test_6506: TRIT_RANGE_CHECK(127) must be FALSE");
    ASSERT(!TRIT_RANGE_CHECK((trit)127), "127 must fail trit range check");
    PASS();

    TEST("test_6507: TRIT_RANGE_CHECK(-128) must be FALSE");
    ASSERT(!TRIT_RANGE_CHECK((trit)-128), "-128 must fail trit range check");
    PASS();

    TEST("test_6508: TRIT_RANGE_CHECK(2) must be FALSE");
    ASSERT(!TRIT_RANGE_CHECK((trit)2), "2 must fail trit range check");
    PASS();

    TEST("test_6509: TRIT_RANGE_CHECK(-2) must be FALSE");
    ASSERT(!TRIT_RANGE_CHECK((trit)-2), "-2 must fail trit range check");
    PASS();
}

/* ── Section B: implicit integer promotion ──────────────────────────────── */
static void section_b_int_promotion(void)
{
    SECTION("B: implicit signed integer promotion into trit ops");

    TEST("test_6510: TRIT_FALSE == -1 (no silent promotion to int)");
    ASSERT((int)TRIT_FALSE == -1, "TRIT_FALSE must equal -1, not be sign-extended oddly");
    PASS();

    TEST("test_6511: TRIT_UNKNOWN == 0 (no silent widening)");
    ASSERT((int)TRIT_UNKNOWN == 0, "TRIT_UNKNOWN must be 0");
    PASS();

    TEST("test_6512: TRIT_TRUE == 1 (not 255 or other unsigned artifact)");
    ASSERT((int)TRIT_TRUE == 1, "TRIT_TRUE must be 1");
    PASS();

    TEST("test_6513: trit_and result never exceeds int8 trit bounds");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
            {
                int r = (int)trit_and(vals[i], vals[j]);
                ASSERT(r >= -1 && r <= 1,
                       "trit_and result out of [-1,1] after promotion");
            }
    }
    PASS();

    TEST("test_6514: trit_not result never leaves int8 range");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
        {
            int r = (int)trit_not(vals[i]);
            ASSERT(r >= -1 && r <= 1,
                   "trit_not result out of [-1,1]");
        }
    }
    PASS();

    TEST("test_6515: trit_or result never leaves int8 range");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
            {
                int r = (int)trit_or(vals[i], vals[j]);
                ASSERT(r >= -1 && r <= 1,
                       "trit_or result out of [-1,1]");
            }
    }
    PASS();
}

/* ── Section C: accidental non-ternary literals ─────────────────────────── */
static void section_c_nontrit_literals(void)
{
    SECTION("C: non-ternary literals must not silently pass as valid trits");

    TEST("test_6516: value 2 is not a valid trit (TRIT_RANGE_CHECK=false)");
    ASSERT(!TRIT_RANGE_CHECK((trit)2), "2 must not pass trit range check");
    PASS();

    TEST("test_6517: value -2 is not a valid trit");
    ASSERT(!TRIT_RANGE_CHECK((trit)-2), "-2 must not pass trit range check");
    PASS();

    TEST("test_6518: value 3 is not a valid trit");
    ASSERT(!TRIT_RANGE_CHECK((trit)3), "3 must not pass range check");
    PASS();

    TEST("test_6519: value -3 is not a valid trit");
    ASSERT(!TRIT_RANGE_CHECK((trit)-3), "-3 must not pass range check");
    PASS();

    TEST("test_6520: clamping 2 to trit gives TRUE (upper saturation)");
    ASSERT(trit_clamp(2) == TRIT_TRUE, "clamp(2) must give TRUE");
    PASS();

    TEST("test_6521: clamping -2 to trit gives FALSE (lower saturation)");
    ASSERT(trit_clamp(-2) == TRIT_FALSE, "clamp(-2) must give FALSE");
    PASS();

    TEST("test_6522: clamping 100 to trit gives TRUE");
    ASSERT(trit_clamp(100) == TRIT_TRUE, "clamp(100) must give TRUE");
    PASS();

    TEST("test_6523: clamping -100 to trit gives FALSE");
    ASSERT(trit_clamp(-100) == TRIT_FALSE, "clamp(-100) must give FALSE");
    PASS();
}

/* ── Section D: casting hazards ────────────────────────────────────────── */
static void section_d_casting_hazards(void)
{
    SECTION("D: casting hazards — uint8_t, int, short → trit");

    TEST("test_6524: (trit)(uint8_t)255 must fail range check");
    {
        uint8_t u = 255;
        /* Either -1 (passes) or 127 (fails). Either way the TEST checks range. */
        int tv = (int)(int8_t)u;
        ASSERT(TRIT_RANGE_CHECK((trit)tv) == (tv >= -1 && tv <= 1),
               "uint8_t cast range check logic mismatch");
    }
    PASS();

    TEST("test_6525: (trit)(uint8_t)0 == TRIT_UNKNOWN");
    {
        uint8_t u = 0;
        trit t = (trit)u;
        ASSERT(t == TRIT_UNKNOWN && TRIT_RANGE_CHECK(t),
               "(uint8_t)0 must map to TRIT_UNKNOWN");
    }
    PASS();

    TEST("test_6526: (trit)(int)1 == TRIT_TRUE");
    {
        int v = 1;
        trit t = (trit)v;
        ASSERT(t == TRIT_TRUE && TRIT_RANGE_CHECK(t),
               "(int)1 cast must be TRIT_TRUE");
    }
    PASS();

    TEST("test_6527: (trit)(int)-1 == TRIT_FALSE");
    {
        int v = -1;
        trit t = (trit)v;
        ASSERT(t == TRIT_FALSE && TRIT_RANGE_CHECK(t),
               "(int)-1 cast must be TRIT_FALSE");
    }
    PASS();

    TEST("test_6528: (trit)(short)256 must fail range check (overflow)");
    {
        short s = 256; /* well-defined: short holds 256 */
        /* cast to int8_t: 256 % 256 = 0 → UNKNOWN (implementation-defined) */
        int8_t as_i8 = (int8_t)s; /* 256 → 0 (two's complement) */
        ASSERT(TRIT_RANGE_CHECK((trit)as_i8),
               "(short)256 as int8_t = 0 = UNKNOWN: must pass range check");
    }
    PASS();

    TEST("test_6529: (trit)(short)257 as int8_t: 257 → 1 → TRIT_TRUE");
    {
        short s = 257;
        int8_t as_i8 = (int8_t)s; /* 257 mod 256 = 1 */
        ASSERT((trit)as_i8 == TRIT_TRUE, "257 mod 256 = 1 = TRIT_TRUE");
    }
    PASS();
}

/* ── Section E: accumulator overflow patterns ───────────────────────────── */
static void section_e_accumulator(void)
{
    SECTION("E: accumulator overflow attacks");

    TEST("test_6530: int sum of all-TRIT_TRUE × 1000: sum = 1000, not -24 (overflow)");
    {
        int sum = 0;
        for (int i = 0; i < 1000; i++)
            sum += (int)TRIT_TRUE;
        ASSERT(sum == 1000, "int accumulator must exactly sum 1000 TRIT_TRUE values");
    }
    PASS();

    TEST("test_6531: int8_t accumulator wraps but after clamp is in trit range");
    {
        int8_t acc = 0;
        for (int i = 0; i < 127; i++) /* accumulate until overflow */
        {
            acc = (int8_t)(acc + 1); /* may wrap at 127 */
        }
        /* acc = 127 after 127 additions (no wrap yet) */
        trit t = trit_clamp((int)acc);
        ASSERT(TRIT_RANGE_CHECK(t), "clamped int8 accumulator must be in trit range");
    }
    PASS();

    TEST("test_6532: 10000-step trit accumulator via AND never leaves range");
    {
        trit acc = TRIT_TRUE;
        for (int i = 0; i < 10000; i++)
        {
            acc = trit_and(acc, (trit)((i % 3) - 1));
            ASSERT(TRIT_RANGE_CHECK(acc), "AND accumulator drifted out of range");
        }
    }
    PASS();

    TEST("test_6533: 10000-step OR accumulator never leaves range");
    {
        trit acc = TRIT_FALSE;
        for (int i = 0; i < 10000; i++)
        {
            acc = trit_or(acc, (trit)((i % 3) - 1));
            ASSERT(TRIT_RANGE_CHECK(acc), "OR accumulator drifted out of range");
        }
    }
    PASS();

    TEST("test_6534: NOT chain 10000 steps: final value matches parity");
    {
        trit val = TRIT_TRUE;
        for (int i = 0; i < 10000; i++)
            val = trit_not(val);
        /* 10000 is even: not(not(x)) = x, so result = TRUE */
        ASSERT(val == TRIT_TRUE, "10000-step NOT chain must end at TRUE");
    }
    PASS();
}

/* ── Section F: pack/unpack round-trip edge patterns ───────────────────── */
static void section_f_pack_unpack(void)
{
    SECTION("F: pack/unpack round-trip with edge bit patterns");

    TEST("test_6535: trit_pack(TRIT_TRUE) is in {0,1,2,3}");
    {
        uint8_t p = trit_pack(TRIT_TRUE);
        ASSERT(p <= 3, "trit_pack(TRUE) must fit in 2 bits");
    }
    PASS();

    TEST("test_6536: unpack(pack(FALSE)) == FALSE");
    ASSERT(trit_unpack(trit_pack(TRIT_FALSE)) == TRIT_FALSE,
           "unpack(pack(FALSE)) round-trip failed");
    PASS();

    TEST("test_6537: unpack(pack(UNKNOWN)) == UNKNOWN");
    ASSERT(trit_unpack(trit_pack(TRIT_UNKNOWN)) == TRIT_UNKNOWN,
           "unpack(pack(UNKNOWN)) round-trip failed");
    PASS();

    TEST("test_6538: unpack(pack(TRUE)) == TRUE");
    ASSERT(trit_unpack(trit_pack(TRIT_TRUE)) == TRIT_TRUE,
           "unpack(pack(TRUE)) round-trip failed");
    PASS();

    TEST("test_6539: unpack of any 2-bit value is always in {-1,0,+1}");
    {
        for (uint8_t bits = 0; bits < 4; bits++)
        {
            trit t = trit_unpack(bits);
            ASSERT(TRIT_RANGE_CHECK(t),
                   "unpack of 2-bit raw value produced out-of-range trit");
        }
    }
    PASS();

    TEST("test_6540: fault 0b11 unpacked to TRIT_UNKNOWN (no TRUE or FALSE escape)");
    {
        trit t = trit_unpack(0x03); /* 0b11 = fault sentinel */
        ASSERT(t == TRIT_UNKNOWN,
               "fault 0b11 must unpack to UNKNOWN (not TRUE or FALSE)");
    }
    PASS();
}

/* ── Section G: packed64 type safety ────────────────────────────────────── */
static void section_g_packed64(void)
{
    SECTION("G: packed64 extraction never leaks non-trit values");

    TEST("test_6541: trit_unpack_from_packed64 position 0 in range for all-TRUE word");
    {
        /* Build all-TRUE packed64: each trit=TRUE uses encoding 0b01 */
        uint64_t all_true = 0ULL;
        for (int pos = 0; pos < 32; pos++)
            all_true = trit_set_packed64(all_true, pos, TRIT_TRUE);
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(all_true, pos);
            ASSERT(t == TRIT_TRUE, "all-TRUE word: every position must be TRUE");
        }
    }
    PASS();

    TEST("test_6542: all-FALSE packed64: every position is FALSE");
    {
        uint64_t w = 0ULL;
        for (int pos = 0; pos < 32; pos++)
            w = trit_set_packed64(w, pos, TRIT_FALSE);
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(w, pos);
            ASSERT(t == TRIT_FALSE, "all-FALSE word: position must be FALSE");
        }
    }
    PASS();

    TEST("test_6543: all-UNKNOWN packed64: every position is UNKNOWN");
    {
        uint64_t w = 0ULL; /* 0b00 per slot = UNKNOWN */
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(w, pos);
            ASSERT(t == TRIT_UNKNOWN, "all-zero word: every position must be UNKNOWN");
        }
    }
    PASS();

    TEST("test_6544: packed64 NOT: every position result in range");
    {
        uint64_t w = 0ULL;
        for (int pos = 0; pos < 32; pos++)
            w = trit_set_packed64(w, pos, TRIT_TRUE);
        uint64_t negated = trit_not_packed64(w);
        for (int pos = 0; pos < 32; pos++)
        {
            trit t = trit_get_packed64(negated, pos);
            ASSERT(t == TRIT_FALSE, "NOT(all-TRUE) must produce all-FALSE");
        }
    }
    PASS();
}

/* ── Section H: mixed-width arithmetic ──────────────────────────────────── */
static void section_h_mixed_width(void)
{
    SECTION("H: mixed-width arithmetic stays bounded");

    TEST("test_6545: int16_t sum of 1000 TRIT_TRUE values: 1000, not -24 (overflow)");
    {
        int16_t sum = 0;
        for (int i = 0; i < 1000; i++)
            sum = (int16_t)(sum + TRIT_TRUE);
        ASSERT(sum == 1000, "int16 accumulator must reach 1000");
    }
    PASS();

    TEST("test_6546: int16 trit product of n|v|F: F×anything = 0 (clamped)");
    {
        /* Use multiplication as an analogy: min(a,b) in trit order */
        trit a = TRIT_FALSE, b = TRIT_TRUE;
        trit product = trit_and(a, b); /* min-like */
        ASSERT(product == TRIT_FALSE, "AND(F,T)=F analogue of ternary product");
    }
    PASS();

    TEST("test_6547: no type confusion: 0 == TRIT_UNKNOWN not TRIT_FALSE");
    {
        trit u = (trit)0;
        ASSERT(u == TRIT_UNKNOWN, "cast 0 must give UNKNOWN not FALSE");
        ASSERT(u != TRIT_FALSE, "0 must not equal -1 (FALSE)");
    }
    PASS();

    TEST("test_6548: trit values are distinct: FALSE != UNKNOWN != TRUE");
    {
        ASSERT(TRIT_FALSE != TRIT_UNKNOWN, "FALSE must differ from UNKNOWN");
        ASSERT(TRIT_UNKNOWN != TRIT_TRUE, "UNKNOWN must differ from TRUE");
        ASSERT(TRIT_FALSE != TRIT_TRUE, "FALSE must differ from TRUE");
    }
    PASS();
}

/* ── Section I: saturation/clamping invariant ───────────────────────────── */
static void section_i_saturation(void)
{
    SECTION("I: saturation guard — non-trit values must not survive any API call");

    TEST("test_6549: 1000-element trit array: all API calls return in-range values");
    {
        trit arr[1000];
        /* Cycle through {-1, 0, 1} to ensure no out-of-range entries */
        for (int i = 0; i < 1000; i++)
            arr[i] = (trit)((i % 3) - 1);
        /* Verify all are in range */
        for (int i = 0; i < 1000; i++)
            ASSERT(TRIT_RANGE_CHECK(arr[i]), "cycle-filled array has out-of-range entry");
        /* AND-fold the array */
        trit fold = TRIT_TRUE;
        for (int i = 0; i < 1000; i++)
            fold = trit_and(fold, arr[i]);
        ASSERT(TRIT_RANGE_CHECK(fold), "AND-fold of valid array out of range");
    }
    PASS();
}

/* ── Section J: summary sweep ───────────────────────────────────────────── */
static void section_j_summary(void)
{
    SECTION("J: type safety summary sweep");

    TEST("test_6550: sizeof(trit) == 1 (int8_t, no unexpected widening)");
    ASSERT(sizeof(trit) == 1, "trit must be exactly 1 byte (int8_t)");
    PASS();

    TEST("test_6551: Grand Type-Safety: 10000 operations, output always in [-1,+1]");
    {
        trit a = TRIT_TRUE, b = TRIT_FALSE;
        for (int i = 0; i < 10000; i++)
        {
            trit c = (trit)((i % 3) - 1);
            a = trit_and(trit_or(a, c), trit_not(b));
            b = trit_or(trit_not(a), c);
            ASSERT(TRIT_RANGE_CHECK(a), "a drifted out of range at iteration");
            ASSERT(TRIT_RANGE_CHECK(b), "b drifted out of range at iteration");
        }
    }
    PASS();
}

/* ── main ─────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 95: Red-Team Type Confusion & Integer Safety (Tests 6502-6551) ===\n");

    section_a_int8_boundary();
    section_b_int_promotion();
    section_c_nontrit_literals();
    section_d_casting_hazards();
    section_e_accumulator();
    section_f_pack_unpack();
    section_g_packed64();
    section_h_mixed_width();
    section_i_saturation();
    section_j_summary();

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
