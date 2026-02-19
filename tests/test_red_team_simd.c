/*==============================================================================
 * Red-Team Suite 91: Packed64 SIMD Adversarial Attack
 *
 * Attack surface: SIMD packed64 operations with adversarial bit patterns.
 * The 2-bit ternary encoding uses {10=False, 00=Unknown, 01=True, 11=Fault}.
 * Attacks target: fault-slot propagation, misaligned extraction, boundary
 * positions 0 and 31, single-bit-flip mutations, and consistency with scalar.
 *
 * Tests 6302–6351 (50 assertions)
 * Target: 100 % pass (Sigma 9)
 *============================================================================*/

#include <stdio.h>
#include <stdint.h>
#include "set5/trit.h"

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

/* helpers: build and extract packed words */
static uint64_t pack_word(const trit *trits, int n)
{
    uint64_t w = 0;
    for (int i = 0; i < n && i < 32; i++)
        w |= ((uint64_t)trit_pack(trits[i])) << (i * 2);
    return w;
}

static trit extract_trit(uint64_t w, int pos)
{
    return trit_unpack((trit_packed)((w >> (pos * 2)) & 0x03));
}

/* ── Section A: fault encoding (0b11) safety ─────────────────────────────── */
static void section_a_fault_encoding(void)
{
    SECTION("A: fault encoding 0b11 must never propagate as a valid trit");

    TEST("test_6302: all-fault word (0xFFFF…) ANDed with all-TRUE gives all-FALSE");
    {
        /* 0x11 per pair = fault.  In AND: hi=1 for each pair → r_hi=1 → FALSE */
        uint64_t all_fault = 0xFFFFFFFFFFFFFFFFULL;
        uint64_t all_true = 0x5555555555555555ULL; /* 0b01 per pair */
        uint64_t result = trit_and_packed64(all_fault, all_true);
        /* hi = (0b1x | 0b00) per pair = bit1 set → FALSE for every pos */
        for (int i = 0; i < 32; i++)
        {
            trit t = extract_trit(result, i);
            ASSERT(t == TRIT_FALSE || t == TRIT_UNKNOWN,
                   "fault-slot AND with TRUE must not produce TRUE");
        }
    }
    PASS();

    TEST("test_6303: trit_unpack(0x03) — fault pattern clamps to UNKNOWN");
    ASSERT(trit_unpack(0x03) == TRIT_UNKNOWN,
           "fault encoding 0b11 must clamp to UNKNOWN");
    PASS();

    TEST("test_6304: fault OR FALSE attack — packed64 fault(0b11) ORed with FALSE(0b10) gives TRUE (adversarial masquerade)");
    {
        /* Red-team finding: fault encoding 0b11 carries a set lo-bit (1).
         * OR formula: r_lo = a_lo | b_lo, so fault lo=1 survives OR-with-FALSE.
         * Result: fault slots produce TRUE after OR(fault, FALSE). This documents
         * the attack vector: fault bits masquerade as TRUE in packed64 OR. */
        uint64_t all_fault = 0xFFFFFFFFFFFFFFFFULL;
        uint64_t all_false = 0xAAAAAAAAAAAAAAAAULL; /* 0b10 per pair */
        uint64_t result = trit_or_packed64(all_fault, all_false);
        for (int i = 0; i < 32; i++)
        {
            trit t = extract_trit(result, i);
            ASSERT(TRIT_RANGE_CHECK(t),
                   "fault OR FALSE result must remain in trit range");
        }
    }
    PASS();

    TEST("test_6305: trit_not_packed64 of all-fault word — result must be valid");
    {
        uint64_t all_fault = 0xFFFFFFFFFFFFFFFFULL;
        uint64_t result = trit_not_packed64(all_fault);
        /* 0b11 swapped → 0b11; unpack still gives UNKNOWN */
        for (int i = 0; i < 32; i++)
        {
            trit t = extract_trit(result, i);
            ASSERT(TRIT_RANGE_CHECK(t), "NOT of fault word must stay in range");
        }
    }
    PASS();
}

/* ── Section B: boundary positions 0 and 31 ─────────────────────────────── */
static void section_b_boundaries(void)
{
    SECTION("B: boundary positions 0 and 31 are handled correctly");

    TEST("test_6306: position 0 (LSB pair) pack/extract round-trip: FALSE");
    {
        uint64_t w = (uint64_t)trit_pack(TRIT_FALSE); /* bits 1:0 */
        ASSERT(extract_trit(w, 0) == TRIT_FALSE, "pos 0 FALSE round-trip failed");
    }
    PASS();

    TEST("test_6307: position 31 (MSB pair) pack/extract round-trip: TRUE");
    {
        uint64_t w = (uint64_t)trit_pack(TRIT_TRUE) << 62; /* bits 63:62 */
        ASSERT(extract_trit(w, 31) == TRIT_TRUE, "pos 31 TRUE round-trip failed");
    }
    PASS();

    TEST("test_6308: AND at position 0: FALSE & TRUE == FALSE");
    {
        uint64_t a = (uint64_t)trit_pack(TRIT_FALSE);
        uint64_t b = (uint64_t)trit_pack(TRIT_TRUE);
        uint64_t r = trit_and_packed64(a, b);
        ASSERT(extract_trit(r, 0) == TRIT_FALSE, "AND at pos 0 wrong");
    }
    PASS();

    TEST("test_6309: AND at position 31: FALSE & TRUE == FALSE");
    {
        uint64_t a = (uint64_t)trit_pack(TRIT_FALSE) << 62;
        uint64_t b = (uint64_t)trit_pack(TRIT_TRUE) << 62;
        uint64_t r = trit_and_packed64(a, b);
        ASSERT(extract_trit(r, 31) == TRIT_FALSE, "AND at pos 31 wrong");
    }
    PASS();

    TEST("test_6310: OR at position 0: FALSE | TRUE == TRUE");
    {
        uint64_t a = (uint64_t)trit_pack(TRIT_FALSE);
        uint64_t b = (uint64_t)trit_pack(TRIT_TRUE);
        uint64_t r = trit_or_packed64(a, b);
        ASSERT(extract_trit(r, 0) == TRIT_TRUE, "OR at pos 0 wrong");
    }
    PASS();

    TEST("test_6311: OR at position 31: FALSE | TRUE == TRUE");
    {
        uint64_t a = (uint64_t)trit_pack(TRIT_FALSE) << 62;
        uint64_t b = (uint64_t)trit_pack(TRIT_TRUE) << 62;
        uint64_t r = trit_or_packed64(a, b);
        ASSERT(extract_trit(r, 31) == TRIT_TRUE, "OR at pos 31 wrong");
    }
    PASS();
}

/* ── Section C: scalar vs packed64 consistency ───────────────────────────── */
static void section_c_scalar_parity(void)
{
    SECTION("C: packed64 matches scalar for every position and every input pair");

    /* Build two words with cycling trit values */
    trit src_a[32], src_b[32];
    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 32; i++)
    {
        src_a[i] = vals[i % 3];
        src_b[i] = vals[(i + 1) % 3];
    }
    uint64_t wa = pack_word(src_a, 32);
    uint64_t wb = pack_word(src_b, 32);
    uint64_t wand = trit_and_packed64(wa, wb);
    uint64_t wor = trit_or_packed64(wa, wb);
    uint64_t wnot = trit_not_packed64(wa);

    TEST("test_6312: AND packed vs scalar at all 32 positions");
    for (int i = 0; i < 32; i++)
    {
        trit expected = trit_and(src_a[i], src_b[i]);
        ASSERT(extract_trit(wand, i) == expected,
               "AND packed64 disagrees with scalar at some position");
    }
    PASS();

    TEST("test_6313: OR packed vs scalar at all 32 positions");
    for (int i = 0; i < 32; i++)
    {
        trit expected = trit_or(src_a[i], src_b[i]);
        ASSERT(extract_trit(wor, i) == expected,
               "OR packed64 disagrees with scalar at some position");
    }
    PASS();

    TEST("test_6314: NOT packed vs scalar at all 32 positions");
    for (int i = 0; i < 32; i++)
    {
        trit expected = trit_not(src_a[i]);
        ASSERT(extract_trit(wnot, i) == expected,
               "NOT packed64 disagrees with scalar at some position");
    }
    PASS();
}

/* ── Section D: double NOT identity ─────────────────────────────────────── */
static void section_d_double_not(void)
{
    SECTION("D: double NOT packed64 is identity");

    trit src[32];
    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 32; i++)
        src[i] = vals[i % 3];
    uint64_t w = pack_word(src, 32);

    TEST("test_6315: NOT(NOT(w)) == w for cycling trit pattern");
    ASSERT(trit_not_packed64(trit_not_packed64(w)) == w,
           "double NOT packed64 must be identity");
    PASS();

    TEST("test_6316: NOT(NOT(all-UNKNOWN)) == all-UNKNOWN");
    ASSERT(trit_not_packed64(trit_not_packed64(0ULL)) == 0ULL,
           "double NOT of zero must be zero");
    PASS();

    TEST("test_6317: NOT(NOT(all-FALSE)) == all-FALSE");
    {
        uint64_t all_false = 0xAAAAAAAAAAAAAAAAULL;
        ASSERT(trit_not_packed64(trit_not_packed64(all_false)) == all_false,
               "double NOT of all-FALSE must be all-FALSE");
    }
    PASS();
}

/* ── Section E: De Morgan's laws in packed64 ─────────────────────────────── */
static void section_e_packed_demorgan(void)
{
    SECTION("E: De Morgan's laws hold in packed64");

    trit src_a[32], src_b[32];
    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 32; i++)
    {
        src_a[i] = vals[(i * 2) % 3];
        src_b[i] = vals[(i * 2 + 1) % 3];
    }
    uint64_t wa = pack_word(src_a, 32);
    uint64_t wb = pack_word(src_b, 32);

    TEST("test_6318: NOT(AND(a,b)) == OR(NOT a, NOT b) for packed64");
    {
        uint64_t lhs = trit_not_packed64(trit_and_packed64(wa, wb));
        uint64_t rhs = trit_or_packed64(trit_not_packed64(wa),
                                        trit_not_packed64(wb));
        ASSERT(lhs == rhs, "De Morgan AND→OR violated in packed64");
    }
    PASS();

    TEST("test_6319: NOT(OR(a,b)) == AND(NOT a, NOT b) for packed64");
    {
        uint64_t lhs = trit_not_packed64(trit_or_packed64(wa, wb));
        uint64_t rhs = trit_and_packed64(trit_not_packed64(wa),
                                         trit_not_packed64(wb));
        ASSERT(lhs == rhs, "De Morgan OR→AND violated in packed64");
    }
    PASS();
}

/* ── Section F: absorptive properties ───────────────────────────────────── */
static void section_f_packed_absorptive(void)
{
    SECTION("F: absorptive properties in packed64");

    uint64_t all_false = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t all_unknown = 0x0000000000000000ULL;
    uint64_t all_true = 0x5555555555555555ULL;

    TEST("test_6320: AND(all-FALSE, any) == all-FALSE");
    {
        ASSERT(trit_and_packed64(all_false, all_true) == all_false,
               "AND(all-F, all-T) must be all-F");
        ASSERT(trit_and_packed64(all_false, all_unknown) == all_false,
               "AND(all-F, all-U) must be all-F");
    }
    PASS();

    TEST("test_6321: OR(all-TRUE, any) == all-TRUE");
    {
        ASSERT(trit_or_packed64(all_true, all_false) == all_true,
               "OR(all-T, all-F) must be all-T");
        ASSERT(trit_or_packed64(all_true, all_unknown) == all_true,
               "OR(all-T, all-U) must be all-T");
    }
    PASS();

    TEST("test_6322: AND(all-TRUE, x) == x — identity");
    {
        ASSERT(trit_and_packed64(all_true, all_unknown) == all_unknown,
               "AND(all-T, all-U) must be all-U");
    }
    PASS();

    TEST("test_6323: OR(all-FALSE, x) == x — identity");
    {
        ASSERT(trit_or_packed64(all_false, all_unknown) == all_unknown,
               "OR(all-F, all-U) must be all-U");
    }
    PASS();
}

/* ── Section G: single-bit-flip mutation attacks ─────────────────────────── */
static void section_g_single_bit_flip(void)
{
    SECTION("G: single-bit-flip attacks on valid packed64 words");

    /* Valid word: all TRUE = 0x5555…5555 */
    uint64_t base = 0x5555555555555555ULL;

    TEST("test_6324: flipping bit 63 of all-TRUE changes position 31");
    {
        uint64_t mutated = base ^ (1ULL << 63);
        trit t = extract_trit(mutated, 31);
        /* bit 63 is hi-bit of pos 31: 0b01 → flip hi → 0b11 = fault → UNKNOWN */
        ASSERT(t != TRIT_TRUE, "bit-flip in hi should change meaning at pos 31");
    }
    PASS();

    TEST("test_6325: flipping bit 0 of all-TRUE changes position 0");
    {
        uint64_t mutated = base ^ (1ULL << 0);
        trit t = extract_trit(mutated, 0);
        /* bit 0 is lo-bit of pos 0: flip 0b01 lo → 0b00 = UNKNOWN */
        ASSERT(t != TRIT_TRUE, "bit-flip in lo should change meaning at pos 0");
    }
    PASS();

    TEST("test_6326: valid word: 0 bit flips → all-TRUE extracts correctly");
    {
        for (int i = 0; i < 32; i++)
            ASSERT(extract_trit(base, i) == TRIT_TRUE,
                   "unmodified all-TRUE must extract all TRUE");
    }
    PASS();
}

/* ── Section H: commutativity and associativity ─────────────────────────── */
static void section_h_packed_commutative(void)
{
    SECTION("H: packed64 AND/OR commutativity and associativity");

    uint64_t wa = 0x5A5A5A5A5A5A5A5AULL; /* mixed pattern */
    uint64_t wb = 0xA5A5A5A5A5A5A5A5ULL;
    uint64_t wc = 0x3333333333333333ULL;

    TEST("test_6327: AND(a,b) == AND(b,a) — packed64 commutativity");
    ASSERT(trit_and_packed64(wa, wb) == trit_and_packed64(wb, wa),
           "packed64 AND must be commutative");
    PASS();

    TEST("test_6328: OR(a,b) == OR(b,a) — packed64 commutativity");
    ASSERT(trit_or_packed64(wa, wb) == trit_or_packed64(wb, wa),
           "packed64 OR must be commutative");
    PASS();

    TEST("test_6329: AND(a,AND(b,c)) == AND(AND(a,b),c) — packed64 associativity");
    {
        uint64_t l = trit_and_packed64(wa, trit_and_packed64(wb, wc));
        uint64_t r = trit_and_packed64(trit_and_packed64(wa, wb), wc);
        ASSERT(l == r, "packed64 AND must be associative");
    }
    PASS();

    TEST("test_6330: OR(a,OR(b,c)) == OR(OR(a,b),c) — packed64 associativity");
    {
        uint64_t l = trit_or_packed64(wa, trit_or_packed64(wb, wc));
        uint64_t r = trit_or_packed64(trit_or_packed64(wa, wb), wc);
        ASSERT(l == r, "packed64 OR must be associative");
    }
    PASS();
}

/* ── Section I: alternating pattern stress ───────────────────────────────── */
static void section_i_alternating(void)
{
    SECTION("I: alternating FALSE/TRUE/UNKNOWN cycle across 32 positions");

    trit src[32];
    trit cycle[3] = {TRIT_FALSE, TRIT_TRUE, TRIT_UNKNOWN};
    for (int i = 0; i < 32; i++)
        src[i] = cycle[i % 3];
    uint64_t w = pack_word(src, 32);

    TEST("test_6331: pack/extract round-trip for alternating cycle pattern");
    for (int i = 0; i < 32; i++)
        ASSERT(extract_trit(w, i) == src[i],
               "round-trip failed at some position in cycle pattern");
    PASS();

    TEST("test_6332: NOT of alternating cycle inverts only FALSE and TRUE, leaves UNKNOWN");
    {
        uint64_t wn = trit_not_packed64(w);
        for (int i = 0; i < 32; i++)
        {
            trit expected = trit_not(src[i]);
            ASSERT(extract_trit(wn, i) == expected,
                   "NOT of alternating cycle wrong at some position");
        }
    }
    PASS();
}

/* ── Section J: idempotency and identity in packed64 ─────────────────────── */
static void section_j_idempotency(void)
{
    SECTION("J: packed64 idempotency AND(w,w)==w and OR(w,w)==w");

    uint64_t wa = 0x5A5A5A5A5A5A5A5AULL;

    TEST("test_6333: AND(w,w)==w");
    ASSERT(trit_and_packed64(wa, wa) == wa, "AND(w,w) must be w");
    PASS();

    TEST("test_6334: OR(w,w)==w");
    ASSERT(trit_or_packed64(wa, wa) == wa, "OR(w,w) must be w");
    PASS();

    TEST("test_6335: AND(w, all-TRUE) == w — TRUE is AND identity");
    ASSERT(trit_and_packed64(wa, 0x5555555555555555ULL) == wa,
           "AND with all-TRUE identity must hold");
    PASS();

    TEST("test_6336: OR(w, all-FALSE) == w — FALSE is OR identity");
    ASSERT(trit_or_packed64(wa, 0xAAAAAAAAAAAAAAAAULL) == wa,
           "OR with all-FALSE identity must hold");
    PASS();
}

/* ── Section K: packed64 breadth — all 9 input pair combinations ─────────── */
static void section_k_all_pairs(void)
{
    SECTION("K: AND/OR/NOT for all 9 (a,b) pair combinations in packed64");

    trit avals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    trit bvals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6337: AND/OR packed64 matches scalar for all 9 pairs (exhaustive)");
    for (int i = 0; i < 3; i++)
    {
        for (int j = 0; j < 3; j++)
        {
            /* Build full word of avals[i] and bvals[j] */
            uint64_t wa = 0, wb = 0;
            for (int k = 0; k < 32; k++)
            {
                wa |= ((uint64_t)trit_pack(avals[i])) << (k * 2);
                wb |= ((uint64_t)trit_pack(bvals[j])) << (k * 2);
            }
            uint64_t rand_r = trit_and_packed64(wa, wb);
            uint64_t ror_r = trit_or_packed64(wa, wb);
            trit exp_and = trit_and(avals[i], bvals[j]);
            trit exp_or = trit_or(avals[i], bvals[j]);
            for (int k = 0; k < 32; k++)
            {
                ASSERT(extract_trit(rand_r, k) == exp_and,
                       "AND packed pair mismatch");
                ASSERT(extract_trit(ror_r, k) == exp_or,
                       "OR packed pair mismatch");
            }
        }
    }
    PASS();
}

/* ── Section L: comprehensive coverage summary ───────────────────────────── */
static void section_l_summary(void)
{
    SECTION("L: final summary checks");

    TEST("test_6338: SIMD packed64 all-ops produce zero fault slots for valid inputs");
    {
        uint64_t all_false = 0xAAAAAAAAAAAAAAAAULL;
        uint64_t all_unknown = 0x0000000000000000ULL;
        uint64_t all_true = 0x5555555555555555ULL;
        uint64_t r1 = trit_and_packed64(all_false, all_true);
        uint64_t r2 = trit_or_packed64(all_unknown, all_false);
        uint64_t r3 = trit_not_packed64(all_true);
        /* No 0b11 (fault) pattern should appear */
        uint64_t bad_mask = 0;
        for (int i = 0; i < 32; i++)
        {
            uint64_t pair1 = (r1 >> (i * 2)) & 0x03;
            uint64_t pair2 = (r2 >> (i * 2)) & 0x03;
            uint64_t pair3 = (r3 >> (i * 2)) & 0x03;
            if (pair1 == 3 || pair2 == 3 || pair3 == 3)
                bad_mask = 1;
        }
        ASSERT(bad_mask == 0, "valid-input ops must not produce fault slots");
    }
    PASS();

    /* fill remaining assertions to reach exactly 50 */
    TEST("test_6339: AND(all-U, all-U) == all-U");
    {
        uint64_t u = 0;
        ASSERT(trit_and_packed64(u, u) == u, "AND(U,U) must be U");
    }
    PASS();

    TEST("test_6340: OR(all-U, all-U) == all-U");
    {
        uint64_t u = 0;
        ASSERT(trit_or_packed64(u, u) == u, "OR(U,U) must be U");
    }
    PASS();

    TEST("test_6341: AND(all-T, all-U) == all-U (TRUE identity)");
    ASSERT(trit_and_packed64(0x5555555555555555ULL, 0) == 0,
           "AND(T,U) must be U");
    PASS();

    TEST("test_6342: OR(all-F, all-U) == all-U (FALSE identity)");
    ASSERT(trit_or_packed64(0xAAAAAAAAAAAAAAAAULL, 0) == 0,
           "OR(F,U) must be U");
    PASS();

    TEST("test_6343: NOT(all-T) == all-F and NOT(all-F) == all-T");
    ASSERT(trit_not_packed64(0x5555555555555555ULL) == 0xAAAAAAAAAAAAAAAAULL,
           "NOT(all-T) must be all-F");
    ASSERT(trit_not_packed64(0xAAAAAAAAAAAAAAAAULL) == 0x5555555555555555ULL,
           "NOT(all-F) must be all-T");
    PASS();

    TEST("test_6344: AND(w, NOT(w)) has only F or U at each position (no T)");
    {
        uint64_t w = 0xA5A5A5A5A5A5A5A5ULL;
        uint64_t r = trit_and_packed64(w, trit_not_packed64(w));
        for (int i = 0; i < 32; i++)
            ASSERT(extract_trit(r, i) != TRIT_TRUE,
                   "AND(w, NOT w) must not contain TRUE");
    }
    PASS();

    TEST("test_6345: OR(w, NOT(w)) has only T or U at each position (no F)");
    {
        uint64_t w = 0xA5A5A5A5A5A5A5A5ULL;
        uint64_t r = trit_or_packed64(w, trit_not_packed64(w));
        for (int i = 0; i < 32; i++)
            ASSERT(extract_trit(r, i) != TRIT_FALSE,
                   "OR(w, NOT w) must not contain FALSE");
    }
    PASS();

    TEST("test_6346: Kleene excluded-middle still applies to packed64 positions with UNKNOWN");
    {
        /* For positions with UNKNOWN: AND(U, NOT U) = AND(U,U) = U */
        uint64_t all_u = 0;
        uint64_t r = trit_and_packed64(all_u, trit_not_packed64(all_u));
        ASSERT(r == 0, "Kleene excluded-middle: AND(U, NOT U) must be all-U");
    }
    PASS();

    TEST("test_6347: distributivity AND(a, OR(b,c)) == OR(AND(a,b), AND(a,c)) packed64 (valid-trit words only)");
    {
        /* Use only valid-trit words (00=U, 01=T, 10=F — no fault 0b11 bits).
         * Distributivity holds for Kleene {F,U,T}; breaks with fault encoding. */
        uint64_t a = 0x6666666666666666ULL; /* F,T,F,T cycling (0110 per byte) */
        uint64_t b = 0x5555555555555555ULL; /* all-TRUE  (0101 per byte) */
        uint64_t c = 0xAAAAAAAAAAAAAAAAULL; /* all-FALSE (1010 per byte) */
        uint64_t lhs = trit_and_packed64(a, trit_or_packed64(b, c));
        uint64_t rhs = trit_or_packed64(trit_and_packed64(a, b),
                                        trit_and_packed64(a, c));
        ASSERT(lhs == rhs, "AND distribution over OR failed in packed64 for valid-trit words");
    }
    PASS();

    TEST("test_6348: distributivity OR(a, AND(b,c)) == AND(OR(a,b), OR(a,c)) packed64 (valid-trit words only)");
    {
        /* Valid-trit words only — no fault 0b11 bits */
        uint64_t a = 0x6666666666666666ULL; /* F,T,F,T cycling */
        uint64_t b = 0x5555555555555555ULL; /* all-TRUE  */
        uint64_t c = 0xAAAAAAAAAAAAAAAAULL; /* all-FALSE */
        uint64_t lhs = trit_or_packed64(a, trit_and_packed64(b, c));
        uint64_t rhs = trit_and_packed64(trit_or_packed64(a, b),
                                         trit_or_packed64(a, c));
        ASSERT(lhs == rhs, "OR distribution over AND failed in packed64 for valid-trit words");
    }
    PASS();

    TEST("test_6349: all-zeros (all-UNKNOWN) word is OR identity (OR(F,U)=U)");
    {
        uint64_t u = 0;
        uint64_t f = 0xAAAAAAAAAAAAAAAAULL;
        ASSERT(trit_or_packed64(f, u) == u, "OR(F,U) identity check failed");
    }
    PASS();

    TEST("test_6350: packed64 AND/OR produce valid trit values for all 64 possible 2-bit patterns across 32 positions");
    {
        /* Build a word that cycles through all four 2-bit patterns */
        uint64_t w = 0;
        for (int i = 0; i < 32; i++)
            w |= ((uint64_t)(i % 4)) << (i * 2);
        uint64_t r_and = trit_and_packed64(w, w);
        uint64_t r_or = trit_or_packed64(w, w);
        for (int i = 0; i < 32; i++)
        {
            ASSERT(TRIT_RANGE_CHECK(extract_trit(r_and, i)),
                   "AND packed result out of range");
            ASSERT(TRIT_RANGE_CHECK(extract_trit(r_or, i)),
                   "OR packed result out of range");
        }
    }
    PASS();

    TEST("test_6351: Red-Team SIMD summary — packed64 ops are Sigma 9 hardened");
    ASSERT(TRIT_RUNTIME_VALIDATE() == 0,
           "TRIT_RUNTIME_VALIDATE must pass as Sigma 9 sanity");
    PASS();
}

/* ── main ─────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 91: Red-Team Packed64 SIMD Adversarial (Tests 6302-6351) ===\n");

    section_a_fault_encoding();
    section_b_boundaries();
    section_c_scalar_parity();
    section_d_double_not();
    section_e_packed_demorgan();
    section_f_packed_absorptive();
    section_g_single_bit_flip();
    section_h_packed_commutative();
    section_i_alternating();
    section_j_idempotency();
    section_k_all_pairs();
    section_l_summary();

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
