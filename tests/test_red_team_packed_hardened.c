/*==============================================================================
 * Red-Team Suite 97: Packed64 Fault-Hardening Verification
 *
 * Directly verifies the T-SEC mitigations added to trit.h after the
 * fault-injection attack documented in Suite 91 / test_6304:
 *
 *   has_fault_packed64        — O(1) fault slot detector
 *   trit_sanitize_packed64    — fault→UNKNOWN sanitizer
 *   trit_or_packed64_hardened — sanitizing Kleene OR
 *   trit_and_packed64_hardened — sanitizing Kleene AND
 *   trit_not_packed64_hardened — sanitizing Kleene NOT
 *   TRIT_PACKED_VALID          — validity predicate macro
 *
 * Attack reminder (Suite 91):
 *   trit_or_packed64(0xFFFF…=fault, 0xAAAA…=false) = 0x5555…=TRUE
 *   The hardened OR must produce 0x0000…=UNKNOWN (fault→UNKNOWN first).
 *
 * Proof: proof/PackedFaultSemantics.thy
 * Tests 6602–6651 (50 assertions)
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

/* Helpers */
static trit extract_trit_pos(uint64_t w, int pos)
{
    return trit_unpack((trit_packed)((w >> (pos * 2)) & 0x03));
}

static int count_fault_slots(uint64_t w)
{
    int count = 0;
    for (int i = 0; i < 32; i++)
        if (((w >> (i * 2)) & 0x03) == 0x03)
            count++;
    return count;
}

/* ── Section A: has_fault_packed64 detection ────────────────────────────── */
static void section_a_fault_detection(void)
{
    SECTION("A: has_fault_packed64 detects 0b11 slots correctly");

    TEST("test_6602: all-fault word (0xFFFF…) is detected");
    ASSERT(has_fault_packed64(0xFFFFFFFFFFFFFFFFULL) != 0,
           "all-fault word must be detected");
    PASS();

    TEST("test_6603: all-UNKNOWN word (0x0000…) is not a fault");
    ASSERT(has_fault_packed64(0x0000000000000000ULL) == 0,
           "all-UNKNOWN word must not be detected as fault");
    PASS();

    TEST("test_6604: all-TRUE word (0x5555…) is not a fault");
    ASSERT(has_fault_packed64(0x5555555555555555ULL) == 0,
           "all-TRUE word must not be detected as fault");
    PASS();

    TEST("test_6605: all-FALSE word (0xAAAA…) is not a fault");
    ASSERT(has_fault_packed64(0xAAAAAAAAAAAAAAAAULL) == 0,
           "all-FALSE word must not be detected as fault");
    PASS();

    TEST("test_6606: mixed valid word has no fault slots");
    {
        /* 0x6666… = 0110 per byte = T,F per 2-slot pair — all valid */
        uint64_t mixed = 0x6666666666666666ULL;
        ASSERT(has_fault_packed64(mixed) == 0,
               "mixed valid word must not trigger fault detection");
    }
    PASS();

    TEST("test_6607: single fault slot at position 0 is detected");
    {
        uint64_t w = 0x0000000000000003ULL; /* 0b11 at bits [1:0] */
        ASSERT(has_fault_packed64(w) != 0,
               "fault at position 0 must be detected");
    }
    PASS();

    TEST("test_6608: single fault slot at position 31 is detected");
    {
        uint64_t w = (uint64_t)0x03 << 62; /* 0b11 at bits [63:62] */
        ASSERT(has_fault_packed64(w) != 0,
               "fault at position 31 must be detected");
    }
    PASS();

    TEST("test_6609: single fault slot at position 15 is detected");
    {
        uint64_t w = (uint64_t)0x03 << 30; /* 0b11 at bits [31:30] */
        ASSERT(has_fault_packed64(w) != 0,
               "fault at position 15 must be detected");
    }
    PASS();

    TEST("test_6610: valid word with one injected fault slot — detected");
    {
        uint64_t w = 0x5555555555555555ULL; /* all-TRUE */
        w ^= (uint64_t)1 << 5;              /* flip hi-bit of position 2 → 0b11 */
        ASSERT(has_fault_packed64(w) != 0,
               "injected fault slot must be detected");
    }
    PASS();

    TEST("test_6611: TRIT_PACKED_VALID macro: valid word → true, fault word → false");
    ASSERT(TRIT_PACKED_VALID(0x5555555555555555ULL) != 0,
           "TRIT_PACKED_VALID must return non-zero for valid word");
    ASSERT(TRIT_PACKED_VALID(0xFFFFFFFFFFFFFFFFULL) == 0,
           "TRIT_PACKED_VALID must return zero for all-fault word");
    PASS();
}

/* ── Section B: trit_sanitize_packed64 ──────────────────────────────────── */
static void section_b_sanitize(void)
{
    SECTION("B: trit_sanitize_packed64 maps fault→UNKNOWN, preserves valid");

    TEST("test_6612: sanitize(all-fault) == all-UNKNOWN");
    ASSERT(trit_sanitize_packed64(0xFFFFFFFFFFFFFFFFULL) == 0x0000000000000000ULL,
           "all-fault sanitized must become all-UNKNOWN");
    PASS();

    TEST("test_6613: sanitize(all-TRUE) == all-TRUE (unchanged)");
    ASSERT(trit_sanitize_packed64(0x5555555555555555ULL) == 0x5555555555555555ULL,
           "sanitize must preserve all-TRUE word");
    PASS();

    TEST("test_6614: sanitize(all-FALSE) == all-FALSE (unchanged)");
    ASSERT(trit_sanitize_packed64(0xAAAAAAAAAAAAAAAAULL) == 0xAAAAAAAAAAAAAAAAULL,
           "sanitize must preserve all-FALSE word");
    PASS();

    TEST("test_6615: sanitize(all-UNKNOWN) == all-UNKNOWN (unchanged)");
    ASSERT(trit_sanitize_packed64(0x0000000000000000ULL) == 0x0000000000000000ULL,
           "sanitize must preserve all-UNKNOWN word");
    PASS();

    TEST("test_6616: sanitize preserves mixed valid word exactly (0x6666…)");
    {
        uint64_t mixed = 0x6666666666666666ULL;
        ASSERT(trit_sanitize_packed64(mixed) == mixed,
               "sanitize must preserve mixed valid word");
    }
    PASS();

    TEST("test_6617: after sanitize, has_fault_packed64 returns 0");
    ASSERT(has_fault_packed64(trit_sanitize_packed64(0xFFFFFFFFFFFFFFFFULL)) == 0,
           "sanitized all-fault word must have no fault slots");
    PASS();

    TEST("test_6618: sanitize single fault at pos 0 → UNKNOWN at pos 0");
    {
        uint64_t w = 0x0000000000000003ULL;
        uint64_t s = trit_sanitize_packed64(w);
        ASSERT(extract_trit_pos(s, 0) == TRIT_UNKNOWN,
               "fault at pos 0 must sanitize to UNKNOWN");
        ASSERT(count_fault_slots(s) == 0,
               "sanitized word must have 0 fault slots");
    }
    PASS();

    TEST("test_6619: sanitize single fault at pos 31 → UNKNOWN at pos 31");
    {
        uint64_t w = (uint64_t)0x03 << 62;
        uint64_t s = trit_sanitize_packed64(w);
        ASSERT(extract_trit_pos(s, 31) == TRIT_UNKNOWN,
               "fault at pos 31 must sanitize to UNKNOWN");
    }
    PASS();

    TEST("test_6620: sanitize is idempotent: sanitize(sanitize(w)) == sanitize(w)");
    {
        uint64_t w = 0xDEADBEEFCAFEBABEULL; /* arbitrary raw bits */
        uint64_t s1 = trit_sanitize_packed64(w);
        uint64_t s2 = trit_sanitize_packed64(s1);
        ASSERT(s1 == s2, "sanitize must be idempotent");
    }
    PASS();

    TEST("test_6621: sanitize output has all slots in valid trit range");
    {
        uint64_t w = 0xFFFFFFFFFFFFFFFFULL;
        uint64_t s = trit_sanitize_packed64(w);
        for (int i = 0; i < 32; i++)
            ASSERT(TRIT_RANGE_CHECK(extract_trit_pos(s, i)),
                   "sanitized slot must be in trit range");
    }
    PASS();
}

/* ── Section C: trit_or_packed64_hardened ───────────────────────────────── */
static void section_c_hardened_or(void)
{
    SECTION("C: trit_or_packed64_hardened — fault treated as UNKNOWN, not TRUE");

    TEST("test_6622: hardened_or(all-fault, all-FALSE) == all-UNKNOWN (NOT all-TRUE)");
    {
        /* Plain OR gives 0x5555…=TRUE — the attack.
         * Hardened OR must give 0x0000…=UNKNOWN (UNKNOWN OR FALSE = UNKNOWN). */
        uint64_t result = trit_or_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0xAAAAAAAAAAAAAAAAULL);
        uint64_t attack = trit_or_packed64(
            0xFFFFFFFFFFFFFFFFULL, 0xAAAAAAAAAAAAAAAAULL);
        ASSERT(attack == 0x5555555555555555ULL,
               "control: plain OR must exhibit attack (all-TRUE)");
        ASSERT(result == 0x0000000000000000ULL,
               "hardened OR must block attack: fault+false must be UNKNOWN");
    }
    PASS();

    TEST("test_6623: hardened_or(all-fault, all-UNKNOWN) == all-UNKNOWN");
    {
        uint64_t r = trit_or_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0x0000000000000000ULL);
        ASSERT(r == 0x0000000000000000ULL,
               "UNKNOWN OR UNKNOWN must be UNKNOWN");
    }
    PASS();

    TEST("test_6624: hardened_or(all-fault, all-TRUE) == all-TRUE");
    {
        /* After sanitize: UNKNOWN OR TRUE = TRUE — correct Kleene */
        uint64_t r = trit_or_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0x5555555555555555ULL);
        ASSERT(r == 0x5555555555555555ULL,
               "UNKNOWN OR TRUE must be TRUE");
    }
    PASS();

    TEST("test_6625: hardened_or(valid, valid) equals plain or for all-FALSE/all-TRUE");
    {
        uint64_t a = 0xAAAAAAAAAAAAAAAAULL;
        uint64_t b = 0x5555555555555555ULL;
        ASSERT(trit_or_packed64_hardened(a, b) == trit_or_packed64(a, b),
               "hardened OR must equal plain OR for valid inputs");
    }
    PASS();

    TEST("test_6626: hardened_or matches plain or for all 9 valid pair combinations");
    {
        uint64_t words[3] = {
            0x0000000000000000ULL, /* all-U */
            0x5555555555555555ULL, /* all-T */
            0xAAAAAAAAAAAAAAAAULL  /* all-F */
        };
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
                ASSERT(trit_or_packed64_hardened(words[i], words[j]) ==
                           trit_or_packed64(words[i], words[j]),
                       "hardened OR must match plain OR for all valid pairs");
    }
    PASS();

    TEST("test_6627: hardened_or never produces fault slots in output");
    {
        ASSERT(has_fault_packed64(trit_or_packed64_hardened(
                   0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL)) == 0,
               "hardened OR(fault, fault) must have no fault output slots");
        ASSERT(has_fault_packed64(trit_or_packed64_hardened(
                   0xFFFFFFFFFFFFFFFFULL, 0xAAAAAAAAAAAAAAAAULL)) == 0,
               "hardened OR(fault, false) must have no fault output slots");
    }
    PASS();

    TEST("test_6628: hardened_or(all-fault, all-fault) == all-UNKNOWN");
    {
        uint64_t r = trit_or_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL);
        ASSERT(r == 0x0000000000000000ULL,
               "fault OR fault must be UNKNOWN (sanitized to UNKNOWN OR UNKNOWN)");
    }
    PASS();

    TEST("test_6629: hardened_or on mixed fault/valid word at each position");
    {
        /* Word: alternating fault(0b11) at even positions, TRUE(0b01) at odd */
        uint64_t mixed = 0;
        for (int i = 0; i < 32; i++)
            mixed |= (uint64_t)((i % 2 == 0) ? 0x03 : 0x01) << (i * 2);
        uint64_t r = trit_or_packed64_hardened(mixed, 0x0000000000000000ULL);
        /* Even positions: UNKNOWN OR UNKNOWN = UNKNOWN */
        /* Odd positions:  TRUE   OR UNKNOWN = TRUE  */
        for (int i = 0; i < 32; i++)
        {
            trit t = extract_trit_pos(r, i);
            if (i % 2 == 0)
                ASSERT(t == TRIT_UNKNOWN,
                       "sanitized fault slot OR UNKNOWN must be UNKNOWN");
            else
                ASSERT(t == TRIT_TRUE,
                       "TRUE slot OR UNKNOWN must be TRUE");
        }
    }
    PASS();

    TEST("test_6630: hardened_or output is always in valid trit range for any input");
    {
        uint64_t words[4] = {
            0xFFFFFFFFFFFFFFFFULL,
            0xAAAAAAAAAAAAAAAAULL,
            0x5555555555555555ULL,
            0x0000000000000000ULL};
        for (int i = 0; i < 4; i++)
            for (int j = 0; j < 4; j++)
            {
                uint64_t r = trit_or_packed64_hardened(words[i], words[j]);
                for (int k = 0; k < 32; k++)
                    ASSERT(TRIT_RANGE_CHECK(extract_trit_pos(r, k)),
                           "hardened OR result must be in valid trit range");
            }
    }
    PASS();

    TEST("test_6631: TRIT_PACKED_VALID holds for all hardened_or outputs");
    {
        ASSERT(TRIT_PACKED_VALID(trit_or_packed64_hardened(
                   0xFFFFFFFFFFFFFFFFULL, 0xAAAAAAAAAAAAAAAAULL)),
               "TRIT_PACKED_VALID must pass for hardened OR output");
    }
    PASS();
}

/* ── Section D: trit_and_packed64_hardened ──────────────────────────────── */
static void section_d_hardened_and(void)
{
    SECTION("D: trit_and_packed64_hardened — fault treated as UNKNOWN");

    TEST("test_6632: hardened_and(all-fault, all-TRUE) == all-UNKNOWN");
    {
        /* After sanitize: UNKNOWN AND TRUE = UNKNOWN */
        uint64_t r = trit_and_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0x5555555555555555ULL);
        ASSERT(r == 0x0000000000000000ULL,
               "UNKNOWN AND TRUE must be UNKNOWN after sanitize");
    }
    PASS();

    TEST("test_6633: hardened_and(all-fault, all-FALSE) == all-FALSE");
    {
        /* After sanitize: UNKNOWN AND FALSE = FALSE */
        uint64_t r = trit_and_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0xAAAAAAAAAAAAAAAAULL);
        ASSERT(r == 0xAAAAAAAAAAAAAAAAULL,
               "UNKNOWN AND FALSE must be FALSE");
    }
    PASS();

    TEST("test_6634: hardened_and(all-fault, all-UNKNOWN) == all-UNKNOWN");
    {
        uint64_t r = trit_and_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0x0000000000000000ULL);
        ASSERT(r == 0x0000000000000000ULL,
               "UNKNOWN AND UNKNOWN must be UNKNOWN");
    }
    PASS();

    TEST("test_6635: hardened_and(valid, valid) equals plain and for all valid words");
    {
        uint64_t vals[3] = {
            0x0000000000000000ULL,
            0x5555555555555555ULL,
            0xAAAAAAAAAAAAAAAAULL};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
                ASSERT(trit_and_packed64_hardened(vals[i], vals[j]) ==
                           trit_and_packed64(vals[i], vals[j]),
                       "hardened AND must equal plain AND for valid pairs");
    }
    PASS();

    TEST("test_6636: hardened_and(all-fault, all-fault) == all-UNKNOWN");
    {
        uint64_t r = trit_and_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0xFFFFFFFFFFFFFFFFULL);
        ASSERT(r == 0x0000000000000000ULL,
               "fault AND fault must be UNKNOWN");
    }
    PASS();

    TEST("test_6637: hardened_and never produces fault slots in output");
    {
        uint64_t r = trit_and_packed64_hardened(
            0xFFFFFFFFFFFFFFFFULL, 0x5555555555555555ULL);
        ASSERT(has_fault_packed64(r) == 0,
               "hardened AND(fault, valid) output must have no fault slots");
    }
    PASS();

    TEST("test_6638: hardened_and on mixed fault/valid word");
    {
        /* Even positions: fault (0b11), odd positions: TRUE (0b01) */
        uint64_t mixed = 0;
        for (int i = 0; i < 32; i++)
            mixed |= (uint64_t)((i % 2 == 0) ? 0x03 : 0x01) << (i * 2);
        /* AND with all-TRUE */
        uint64_t r = trit_and_packed64_hardened(mixed, 0x5555555555555555ULL);
        /* Even: UNKNOWN AND TRUE = UNKNOWN; Odd: TRUE AND TRUE = TRUE */
        for (int i = 0; i < 32; i++)
        {
            trit t = extract_trit_pos(r, i);
            if (i % 2 == 0)
                ASSERT(t == TRIT_UNKNOWN,
                       "sanitized fault AND TRUE must be UNKNOWN");
            else
                ASSERT(t == TRIT_TRUE,
                       "TRUE AND TRUE must be TRUE");
        }
    }
    PASS();

    TEST("test_6639: De Morgan: NOT(hardened_or(a,b)) == hardened_and(NOT a, NOT b) for valid words");
    {
        uint64_t a = 0x6666666666666666ULL;
        uint64_t b = 0x5555555555555555ULL;
        uint64_t lhs = trit_not_packed64(trit_or_packed64_hardened(a, b));
        uint64_t rhs = trit_and_packed64_hardened(
            trit_not_packed64(a), trit_not_packed64(b));
        ASSERT(lhs == rhs, "De Morgan AND←OR must hold for valid words");
    }
    PASS();

    TEST("test_6640: hardened_and output always in valid trit range");
    {
        uint64_t words[4] = {
            0xFFFFFFFFFFFFFFFFULL,
            0xAAAAAAAAAAAAAAAAULL,
            0x5555555555555555ULL,
            0x0000000000000000ULL};
        for (int i = 0; i < 4; i++)
            for (int j = 0; j < 4; j++)
            {
                uint64_t r = trit_and_packed64_hardened(words[i], words[j]);
                for (int k = 0; k < 32; k++)
                    ASSERT(TRIT_RANGE_CHECK(extract_trit_pos(r, k)),
                           "hardened AND output must be in valid trit range");
            }
    }
    PASS();

    TEST("test_6641: TRIT_PACKED_VALID holds for all hardened_and outputs");
    {
        ASSERT(TRIT_PACKED_VALID(trit_and_packed64_hardened(
                   0xFFFFFFFFFFFFFFFFULL, 0x5555555555555555ULL)),
               "TRIT_PACKED_VALID must pass for hardened AND output");
    }
    PASS();
}

/* ── Section E: trit_not_packed64_hardened + integration ────────────────── */
static void section_e_hardened_not_and_integration(void)
{
    SECTION("E: hardened NOT + combined invariants");

    TEST("test_6642: hardened_not(all-fault) == all-UNKNOWN");
    {
        /* Sanitize: fault→UNKNOWN. NOT(UNKNOWN) = UNKNOWN. */
        uint64_t r = trit_not_packed64_hardened(0xFFFFFFFFFFFFFFFFULL);
        ASSERT(r == 0x0000000000000000ULL,
               "NOT of sanitized fault must be UNKNOWN");
    }
    PASS();

    TEST("test_6643: hardened_not(all-TRUE) == all-FALSE");
    {
        uint64_t r = trit_not_packed64_hardened(0x5555555555555555ULL);
        ASSERT(r == 0xAAAAAAAAAAAAAAAAULL,
               "hardened NOT(all-TRUE) must be all-FALSE");
    }
    PASS();

    TEST("test_6644: hardened_not(all-FALSE) == all-TRUE");
    {
        uint64_t r = trit_not_packed64_hardened(0xAAAAAAAAAAAAAAAAULL);
        ASSERT(r == 0x5555555555555555ULL,
               "hardened NOT(all-FALSE) must be all-TRUE");
    }
    PASS();

    TEST("test_6645: hardened_not(valid) == plain not for valid words");
    {
        uint64_t w = 0x6666666666666666ULL;
        ASSERT(trit_not_packed64_hardened(w) == trit_not_packed64(w),
               "hardened NOT must equal plain NOT for valid word");
    }
    PASS();

    TEST("test_6646: double hardened_not is identity for valid words");
    {
        uint64_t w = 0x6666666666666666ULL;
        ASSERT(trit_not_packed64_hardened(trit_not_packed64_hardened(w)) == w,
               "double hardened NOT must be identity for valid word");
    }
    PASS();

    TEST("test_6647: De Morgan: NOT(hardened_and(a,b)) == hardened_or(NOT a, NOT b) for valid");
    {
        uint64_t a = 0x6666666666666666ULL;
        uint64_t b = 0xAAAAAAAAAAAAAAAAULL;
        uint64_t lhs = trit_not_packed64(trit_and_packed64_hardened(a, b));
        uint64_t rhs = trit_or_packed64_hardened(
            trit_not_packed64(a), trit_not_packed64(b));
        ASSERT(lhs == rhs, "De Morgan OR←AND must hold for valid words");
    }
    PASS();

    TEST("test_6648: sanitize then plain OR == hardened OR (equivalence proof)");
    {
        uint64_t fault = 0xFFFFFFFFFFFFFFFFULL;
        uint64_t false_w = 0xAAAAAAAAAAAAAAAAULL;
        uint64_t via_sanitize = trit_or_packed64(
            trit_sanitize_packed64(fault),
            trit_sanitize_packed64(false_w));
        uint64_t via_hardened = trit_or_packed64_hardened(fault, false_w);
        ASSERT(via_sanitize == via_hardened,
               "sanitize-then-plain-OR must equal hardened-OR");
    }
    PASS();

    TEST("test_6649: mixed 32-slot fault/valid word: hardened ops all in range and no fault output");
    {
        /* Build word: cycling through fault(0b11), T(0b01), F(0b10), U(0b00) */
        uint64_t w = 0;
        for (int i = 0; i < 32; i++)
            w |= (uint64_t)(i % 4) << (i * 2); /* 0=U,1=T,2=F,3=fault */
        ASSERT(!TRIT_PACKED_VALID(w), "test word must have fault slots");
        uint64_t r_or = trit_or_packed64_hardened(w, w);
        uint64_t r_and = trit_and_packed64_hardened(w, w);
        uint64_t r_not = trit_not_packed64_hardened(w);
        ASSERT(TRIT_PACKED_VALID(r_or), "hardened OR output must have no fault");
        ASSERT(TRIT_PACKED_VALID(r_and), "hardened AND output must have no fault");
        ASSERT(TRIT_PACKED_VALID(r_not), "hardened NOT output must have no fault");
        for (int i = 0; i < 32; i++)
        {
            ASSERT(TRIT_RANGE_CHECK(extract_trit_pos(r_or, i)), "or range");
            ASSERT(TRIT_RANGE_CHECK(extract_trit_pos(r_and, i)), "and range");
            ASSERT(TRIT_RANGE_CHECK(extract_trit_pos(r_not, i)), "not range");
        }
    }
    PASS();

    TEST("test_6650: sanitize count: all 32 fault slots replaced in mixed word");
    {
        /* Word with fault at every position */
        uint64_t w = 0xFFFFFFFFFFFFFFFFULL;
        ASSERT(count_fault_slots(w) == 32,
               "all-fault word must have 32 fault slots");
        uint64_t s = trit_sanitize_packed64(w);
        ASSERT(count_fault_slots(s) == 0,
               "sanitized word must have 0 fault slots");
    }
    PASS();

    TEST("test_6651: Sigma 9 summary — hardening ops pass TRIT_RUNTIME_VALIDATE and all invariants");
    {
        ASSERT(TRIT_RUNTIME_VALIDATE() == 0,
               "TRIT_RUNTIME_VALIDATE must pass");
        /* Final invariant: hardened OR blocks the documented attack */
        uint64_t proof =
            trit_or_packed64_hardened(0xFFFFFFFFFFFFFFFFULL,
                                      0xAAAAAAAAAAAAAAAAULL);
        ASSERT(proof != 0x5555555555555555ULL,
               "hardened OR must NOT produce all-TRUE from fault+false (attack blocked)");
        ASSERT(TRIT_PACKED_VALID(proof),
               "hardened OR output must be valid");
    }
    PASS();
}

/* ── main ─────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 97: Red-Team Packed64 Fault-Hardening (Tests 6602-6651) ===\n");

    section_a_fault_detection();
    section_b_sanitize();
    section_c_hardened_or();
    section_d_hardened_and();
    section_e_hardened_not_and_integration();

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
