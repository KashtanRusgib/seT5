/*==============================================================================
 * Batch 114 – Tests 6452-6501: Mixed-Radix & Packed64 SIMD Verification
 * Tests packed64 encode/decode, individual trit get/set, fault detection,
 * SIMD-style parallel AND/OR, mixed-radix conversions, and edge cases.
 * Sigma 9 | Generated: 2026-02-20
 *============================================================================*/
#include <stdio.h>
#include <string.h>
#include <math.h>
#include "set5/trit.h"

#define SECTION(n)          \
    do                      \
    {                       \
        section_name = (n); \
    } while (0)
#define TEST(d)             \
    do                      \
    {                       \
        test_count++;       \
        current_test = (d); \
    } while (0)
#define ASSERT(c, m)                                                                           \
    do                                                                                         \
    {                                                                                          \
        if (!(c))                                                                              \
        {                                                                                      \
            printf("  FAIL [%d]: %s — %s (line %d)\n", test_count, current_test, m, __LINE__); \
            fail_count++;                                                                      \
            return;                                                                            \
        }                                                                                      \
    } while (0)
#define PASS()        \
    do                \
    {                 \
        pass_count++; \
    } while (0)

static int test_count = 0, pass_count = 0, fail_count = 0;
static const char *section_name = NULL, *current_test = NULL;

/* ---- Inline Packed64 helpers ------------------------------------------ */

/* Pack 32 trits into uint64: 2 bits per trit, LSB first.
 * Encoding: False(-1)=0b10, Unknown(0)=0b00, True(+1)=0b01 */
static uint64_t pack32(const trit *trits)
{
    uint64_t w = 0;
    for (int i = 0; i < 32; i++)
    {
        uint64_t p = trit_pack(trits[i]);
        w |= ((uint64_t)p) << (i * 2);
    }
    return w;
}

/* Unpack 32 trits from uint64 */
static void unpack32(uint64_t w, trit *out)
{
    for (int i = 0; i < 32; i++)
    {
        trit_packed p = (trit_packed)((w >> (i * 2)) & 0x03);
        out[i] = trit_unpack(p);
    }
}

/* Get single trit from packed word */
static trit packed_get(uint64_t w, int idx)
{
    trit_packed p = (trit_packed)((w >> (idx * 2)) & 0x03);
    return trit_unpack(p);
}

/* Set single trit in packed word */
static uint64_t packed_set(uint64_t w, int idx, trit val)
{
    uint64_t mask = ~(((uint64_t)0x03) << (idx * 2));
    w &= mask;
    w |= ((uint64_t)trit_pack(val)) << (idx * 2);
    return w;
}

/* Binary→ternary: convert unsigned int to array of trits (base-3, balanced) */
static int bin_to_ternary(unsigned int val, trit *out, int max_trits)
{
    if (val == 0)
    {
        out[0] = 0;
        return 1;
    }
    int i = 0;
    unsigned int v = val;
    while (v > 0 && i < max_trits)
    {
        int rem = v % 3;
        if (rem == 2)
        {
            out[i] = -1;
            v = (v + 1) / 3;
        }
        else if (rem == 0)
        {
            out[i] = 0;
            v /= 3;
        }
        else
        {
            out[i] = 1;
            v /= 3;
        }
        i++;
    }
    return i;
}

/* Ternary→decimal: decode balanced ternary array to int */
static int ternary_to_dec(const trit *arr, int len)
{
    int val = 0, pw = 1;
    for (int i = 0; i < len; i++)
    {
        val += arr[i] * pw;
        pw *= 3;
    }
    return val;
}

/* DOT_TRIT: dot product of two trit vectors using Kleene AND + OR accumulation */
static trit dot_trit(const trit *a, const trit *b, int len)
{
    trit acc = TRIT_FALSE;
    for (int i = 0; i < len; i++)
        acc = trit_or(acc, trit_and(a[i], b[i]));
    return acc;
}

/* ---- Tests ------------------------------------------------------------ */

static void test_6452(void)
{
    SECTION("Packed64: pack/unpack round-trip all-Unknown");
    TEST("All-Unknown trits pack to 0 and unpack correctly");
    trit in[32], out[32];
    memset(in, 0, sizeof(in));
    uint64_t w = pack32(in);
    ASSERT(w == 0, "all-Unknown packs to 0");
    unpack32(w, out);
    for (int i = 0; i < 32; i++)
        ASSERT(out[i] == TRIT_UNKNOWN, "unpack Unknown");
    PASS();
}

static void test_6453(void)
{
    SECTION("Packed64: pack/unpack round-trip all-True");
    TEST("All-True trits pack and unpack correctly");
    trit in[32], out[32];
    for (int i = 0; i < 32; i++)
        in[i] = TRIT_TRUE;
    uint64_t w = pack32(in);
    /* Each True = 0b01 → pattern 0x5555555555555555 */
    ASSERT(w == 0x5555555555555555ULL, "all-True pack");
    unpack32(w, out);
    for (int i = 0; i < 32; i++)
        ASSERT(out[i] == TRIT_TRUE, "unpack True");
    PASS();
}

static void test_6454(void)
{
    SECTION("Packed64: pack/unpack round-trip all-False");
    TEST("All-False trits pack and unpack correctly");
    trit in[32], out[32];
    for (int i = 0; i < 32; i++)
        in[i] = TRIT_FALSE;
    uint64_t w = pack32(in);
    /* Each False = 0b10 → pattern 0xAAAAAAAAAAAAAAAA */
    ASSERT(w == 0xAAAAAAAAAAAAAAAAULL, "all-False pack");
    unpack32(w, out);
    for (int i = 0; i < 32; i++)
        ASSERT(out[i] == TRIT_FALSE, "unpack False");
    PASS();
}

static void test_6455(void)
{
    SECTION("Packed64: alternating T,F pattern");
    TEST("Alternating True/False packs and unpacks");
    trit in[32], out[32];
    for (int i = 0; i < 32; i++)
        in[i] = (i % 2 == 0) ? TRIT_TRUE : TRIT_FALSE;
    uint64_t w = pack32(in);
    unpack32(w, out);
    for (int i = 0; i < 32; i++)
        ASSERT(out[i] == in[i], "alternating mismatch");
    PASS();
}

static void test_6456(void)
{
    SECTION("Packed64: get trit at index 0");
    TEST("packed_get on all-True word returns True at idx 0");
    trit in[32];
    for (int i = 0; i < 32; i++)
        in[i] = TRIT_TRUE;
    uint64_t w = pack32(in);
    ASSERT(packed_get(w, 0) == TRIT_TRUE, "idx 0 True");
    PASS();
}

static void test_6457(void)
{
    SECTION("Packed64: get trit at index 31");
    TEST("packed_get on all-False word returns False at idx 31");
    trit in[32];
    for (int i = 0; i < 32; i++)
        in[i] = TRIT_FALSE;
    uint64_t w = pack32(in);
    ASSERT(packed_get(w, 31) == TRIT_FALSE, "idx 31 False");
    PASS();
}

static void test_6458(void)
{
    SECTION("Packed64: set trit in zero word");
    TEST("packed_set idx 5 to True in zero word");
    uint64_t w = 0;
    w = packed_set(w, 5, TRIT_TRUE);
    ASSERT(packed_get(w, 5) == TRIT_TRUE, "set True at 5");
    ASSERT(packed_get(w, 0) == TRIT_UNKNOWN, "others remain Unknown");
    ASSERT(packed_get(w, 4) == TRIT_UNKNOWN, "idx 4 Unknown");
    PASS();
}

static void test_6459(void)
{
    SECTION("Packed64: set then overwrite");
    TEST("Set idx 10 to True, then overwrite to False");
    uint64_t w = 0;
    w = packed_set(w, 10, TRIT_TRUE);
    ASSERT(packed_get(w, 10) == TRIT_TRUE, "first set");
    w = packed_set(w, 10, TRIT_FALSE);
    ASSERT(packed_get(w, 10) == TRIT_FALSE, "overwritten");
    PASS();
}

static void test_6460(void)
{
    SECTION("Packed64: set all 32 individually");
    TEST("Set each trit individually and verify");
    uint64_t w = 0;
    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 32; i++)
        w = packed_set(w, i, vals[i % 3]);
    for (int i = 0; i < 32; i++)
        ASSERT(packed_get(w, i) == vals[i % 3], "individual set check");
    PASS();
}

static void test_6461(void)
{
    SECTION("Packed64: fault detection on clean word");
    TEST("All-True word has no faults");
    ASSERT(!has_fault_packed64(0x5555555555555555ULL), "no fault in all-True");
    PASS();
}

static void test_6462(void)
{
    SECTION("Packed64: fault detection on all-False");
    TEST("All-False word has no faults");
    ASSERT(!has_fault_packed64(0xAAAAAAAAAAAAAAAAULL), "no fault in all-False");
    PASS();
}

static void test_6463(void)
{
    SECTION("Packed64: fault detection on zero (all-Unknown)");
    TEST("All-Unknown word has no faults");
    ASSERT(!has_fault_packed64(0ULL), "no fault in all-Unknown");
    PASS();
}

static void test_6464(void)
{
    SECTION("Packed64: fault detection with 0b11 in slot 0");
    TEST("Fault pattern 0b11 at slot 0 detected");
    uint64_t w = 0x03ULL; /* slot 0 = 0b11 */
    ASSERT(has_fault_packed64(w), "fault detected");
    PASS();
}

static void test_6465(void)
{
    SECTION("Packed64: fault detection with 0b11 in slot 31");
    TEST("Fault pattern at highest slot detected");
    uint64_t w = ((uint64_t)0x03) << 62; /* slot 31 = 0b11 */
    ASSERT(has_fault_packed64(w), "fault at slot 31");
    PASS();
}

static void test_6466(void)
{
    SECTION("Packed64: sanitize clears fault to Unknown");
    TEST("Sanitize fault slot → Unknown (0b00)");
    uint64_t w = 0x03ULL; /* slot 0 = 0b11 = fault */
    uint64_t s = trit_sanitize_packed64(w);
    ASSERT(!has_fault_packed64(s), "sanitized");
    ASSERT(packed_get(s, 0) == TRIT_UNKNOWN, "fault → Unknown");
    PASS();
}

static void test_6467(void)
{
    SECTION("Packed64: sanitize preserves valid slots");
    TEST("Sanitize preserves non-fault slots");
    trit in[32];
    for (int i = 0; i < 32; i++)
        in[i] = TRIT_TRUE;
    uint64_t w = pack32(in);
    uint64_t s = trit_sanitize_packed64(w);
    ASSERT(w == s, "no change for valid word");
    PASS();
}

static void test_6468(void)
{
    SECTION("Packed64: SIMD AND of two all-True words");
    TEST("trit_and_packed64(all-T, all-T) == all-T");
    uint64_t a = 0x5555555555555555ULL; /* all True */
    uint64_t b = 0x5555555555555555ULL;
    uint64_t r = trit_and_packed64(a, b);
    ASSERT(r == 0x5555555555555555ULL, "T AND T = T");
    PASS();
}

static void test_6469(void)
{
    SECTION("Packed64: SIMD AND True with False");
    TEST("trit_and_packed64(all-T, all-F) == all-F");
    uint64_t a = 0x5555555555555555ULL; /* all True */
    uint64_t b = 0xAAAAAAAAAAAAAAAAULL; /* all False */
    uint64_t r = trit_and_packed64(a, b);
    ASSERT(r == 0xAAAAAAAAAAAAAAAAULL, "T AND F = F");
    PASS();
}

static void test_6470(void)
{
    SECTION("Packed64: SIMD AND True with Unknown");
    TEST("trit_and_packed64(all-T, all-U) == all-U");
    uint64_t a = 0x5555555555555555ULL; /* all True */
    uint64_t b = 0ULL;                  /* all Unknown */
    uint64_t r = trit_and_packed64(a, b);
    ASSERT(r == 0ULL, "T AND U = U");
    PASS();
}

static void test_6471(void)
{
    SECTION("Packed64: SIMD AND False with Unknown");
    TEST("trit_and_packed64(all-F, all-U) == all-F");
    uint64_t a = 0xAAAAAAAAAAAAAAAAULL; /* all False */
    uint64_t b = 0ULL;                  /* all Unknown */
    uint64_t r = trit_and_packed64(a, b);
    ASSERT(r == 0xAAAAAAAAAAAAAAAAULL, "F AND U = F");
    PASS();
}

static void test_6472(void)
{
    SECTION("Packed64: SIMD OR of two all-False words");
    TEST("trit_or_packed64(all-F, all-F) == all-F");
    uint64_t a = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t b = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t r = trit_or_packed64(a, b);
    ASSERT(r == 0xAAAAAAAAAAAAAAAAULL, "F OR F = F");
    PASS();
}

static void test_6473(void)
{
    SECTION("Packed64: SIMD OR True with False");
    TEST("trit_or_packed64(all-T, all-F) == all-T");
    uint64_t a = 0x5555555555555555ULL;
    uint64_t b = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t r = trit_or_packed64(a, b);
    ASSERT(r == 0x5555555555555555ULL, "T OR F = T");
    PASS();
}

static void test_6474(void)
{
    SECTION("Packed64: SIMD OR False with Unknown");
    TEST("trit_or_packed64(all-F, all-U) == all-U");
    uint64_t a = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t b = 0ULL;
    uint64_t r = trit_or_packed64(a, b);
    ASSERT(r == 0ULL, "F OR U = U");
    PASS();
}

static void test_6475(void)
{
    SECTION("Packed64: SIMD OR True with Unknown");
    TEST("trit_or_packed64(all-T, all-U) == all-T");
    uint64_t a = 0x5555555555555555ULL;
    uint64_t b = 0ULL;
    uint64_t r = trit_or_packed64(a, b);
    ASSERT(r == 0x5555555555555555ULL, "T OR U = T");
    PASS();
}

static void test_6476(void)
{
    SECTION("Packed64: SIMD NOT all-True");
    TEST("trit_not_packed64(all-T) == all-F");
    uint64_t a = 0x5555555555555555ULL;
    uint64_t r = trit_not_packed64(a);
    ASSERT(r == 0xAAAAAAAAAAAAAAAAULL, "NOT T = F");
    PASS();
}

static void test_6477(void)
{
    SECTION("Packed64: SIMD NOT all-False");
    TEST("trit_not_packed64(all-F) == all-T");
    uint64_t a = 0xAAAAAAAAAAAAAAAAULL;
    uint64_t r = trit_not_packed64(a);
    ASSERT(r == 0x5555555555555555ULL, "NOT F = T");
    PASS();
}

static void test_6478(void)
{
    SECTION("Packed64: SIMD NOT all-Unknown");
    TEST("trit_not_packed64(all-U) == all-U");
    ASSERT(trit_not_packed64(0ULL) == 0ULL, "NOT U = U");
    PASS();
}

static void test_6479(void)
{
    SECTION("Mixed-radix: bin→ternary 0");
    TEST("bin_to_ternary(0) → [0], len=1");
    trit out[8];
    int len = bin_to_ternary(0, out, 8);
    ASSERT(len == 1, "len=1");
    ASSERT(out[0] == 0, "d[0]=0");
    PASS();
}

static void test_6480(void)
{
    SECTION("Mixed-radix: bin→ternary 1");
    TEST("bin_to_ternary(1) → [+1], len=1");
    trit out[8];
    int len = bin_to_ternary(1, out, 8);
    ASSERT(len == 1, "len=1");
    ASSERT(out[0] == 1, "d[0]=+1");
    PASS();
}

static void test_6481(void)
{
    SECTION("Mixed-radix: bin→ternary 2");
    TEST("bin_to_ternary(2) → [-1,+1], decode=2");
    trit out[8];
    int len = bin_to_ternary(2, out, 8);
    ASSERT(len == 2, "len=2");
    ASSERT(ternary_to_dec(out, len) == 2, "decode=2");
    PASS();
}

static void test_6482(void)
{
    SECTION("Mixed-radix: bin→ternary 10");
    TEST("bin_to_ternary(10) → decode=10");
    trit out[8];
    int len = bin_to_ternary(10, out, 8);
    ASSERT(ternary_to_dec(out, len) == 10, "round-trip 10");
    PASS();
}

static void test_6483(void)
{
    SECTION("Mixed-radix: bin→ternary 100");
    TEST("bin_to_ternary(100) → decode=100");
    trit out[8];
    int len = bin_to_ternary(100, out, 8);
    ASSERT(ternary_to_dec(out, len) == 100, "round-trip 100");
    PASS();
}

static void test_6484(void)
{
    SECTION("Mixed-radix: bin→ternary 243");
    TEST("bin_to_ternary(243) → decode=243");
    trit out[8];
    int len = bin_to_ternary(243, out, 8);
    ASSERT(ternary_to_dec(out, len) == 243, "round-trip 243");
    PASS();
}

static void test_6485(void)
{
    SECTION("Mixed-radix: ternary→dec [+1,+1,+1]=13");
    TEST("ternary_to_dec([1,1,1], 3) == 13");
    trit arr[3] = {1, 1, 1};
    ASSERT(ternary_to_dec(arr, 3) == 13, "1+3+9=13");
    PASS();
}

static void test_6486(void)
{
    SECTION("Mixed-radix: ternary→dec [-1,-1,-1]=-13");
    TEST("ternary_to_dec([-1,-1,-1], 3) == -13");
    trit arr[3] = {-1, -1, -1};
    ASSERT(ternary_to_dec(arr, 3) == -13, "-1-3-9=-13");
    PASS();
}

static void test_6487(void)
{
    SECTION("DOT_TRIT: all-True dot all-True");
    TEST("dot_trit(T,T,T; T,T,T) == T");
    trit a[3] = {1, 1, 1}, b[3] = {1, 1, 1};
    ASSERT(dot_trit(a, b, 3) == TRIT_TRUE, "T dot T = T");
    PASS();
}

static void test_6488(void)
{
    SECTION("DOT_TRIT: all-False dot all-True");
    TEST("dot_trit(F,F,F; T,T,T) == F (AND gives F, OR accumulates F)");
    trit a[3] = {-1, -1, -1}, b[3] = {1, 1, 1};
    /* AND(-1,1)=-1 for each pair, OR of all -1s = -1 */
    ASSERT(dot_trit(a, b, 3) == TRIT_FALSE, "F dot T = F");
    PASS();
}

static void test_6489(void)
{
    SECTION("DOT_TRIT: mixed with Unknown");
    TEST("dot_trit(T,U,F; T,T,T) == T (OR(T,U,F)=T)");
    trit a[3] = {1, 0, -1}, b[3] = {1, 1, 1};
    /* AND(1,1)=1, AND(0,1)=0, AND(-1,1)=-1 → OR(1,0,-1)=1 */
    ASSERT(dot_trit(a, b, 3) == TRIT_TRUE, "mixed dot T");
    PASS();
}

static void test_6490(void)
{
    SECTION("DOT_TRIT: empty vector");
    TEST("dot_trit(len=0) == F (acc starts at False)");
    ASSERT(dot_trit(NULL, NULL, 0) == TRIT_FALSE, "empty dot = F");
    PASS();
}

static void test_6491(void)
{
    SECTION("Packed64: round-trip mixed pattern");
    TEST("Pack {T,F,U,T,F,U,...} and unpack matches");
    trit in[32], out[32];
    trit pattern[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    for (int i = 0; i < 32; i++)
        in[i] = pattern[i % 3];
    uint64_t w = pack32(in);
    unpack32(w, out);
    for (int i = 0; i < 32; i++)
        ASSERT(out[i] == in[i], "mixed pattern mismatch");
    PASS();
}

static void test_6492(void)
{
    SECTION("Packed64: hardened AND same as AND for valid");
    TEST("trit_and_packed64_hardened matches trit_and_packed64 for valid input");
    uint64_t a = 0x5555555555555555ULL; /* all True */
    uint64_t b = 0xAAAAAAAAAAAAAAAAULL; /* all False */
    ASSERT(trit_and_packed64_hardened(a, b) == trit_and_packed64(a, b), "hardened==normal");
    PASS();
}

static void test_6493(void)
{
    SECTION("Packed64: hardened OR same as OR for valid");
    TEST("trit_or_packed64_hardened matches trit_or_packed64 for valid input");
    uint64_t a = 0x5555555555555555ULL;
    uint64_t b = 0ULL;
    ASSERT(trit_or_packed64_hardened(a, b) == trit_or_packed64(a, b), "hardened==normal");
    PASS();
}

static void test_6494(void)
{
    SECTION("Packed64: hardened NOT same as NOT for valid");
    TEST("trit_not_packed64_hardened matches trit_not_packed64 for valid input");
    uint64_t a = 0x5555555555555555ULL;
    ASSERT(trit_not_packed64_hardened(a) == trit_not_packed64(a), "hardened==normal");
    PASS();
}

static void test_6495(void)
{
    SECTION("Packed64: TRIT_PACKED_VALID on clean word");
    TEST("TRIT_PACKED_VALID(all-True) == 1");
    ASSERT(TRIT_PACKED_VALID(0x5555555555555555ULL), "valid");
    PASS();
}

static void test_6496(void)
{
    SECTION("Packed64: TRIT_PACKED_VALID on fault word");
    TEST("TRIT_PACKED_VALID(0b11 at slot 0) == 0");
    ASSERT(!TRIT_PACKED_VALID(0x03ULL), "not valid");
    PASS();
}

static void test_6497(void)
{
    SECTION("Packed64: pack single True at idx 15");
    TEST("Set only idx 15 to True in zero word");
    uint64_t w = packed_set(0, 15, TRIT_TRUE);
    ASSERT(packed_get(w, 15) == TRIT_TRUE, "idx 15 True");
    ASSERT(packed_get(w, 14) == TRIT_UNKNOWN, "idx 14 Unknown");
    ASSERT(packed_get(w, 16) == TRIT_UNKNOWN, "idx 16 Unknown");
    PASS();
}

static void test_6498(void)
{
    SECTION("Packed64: pack single False at idx 0");
    TEST("Set idx 0 to False");
    uint64_t w = packed_set(0, 0, TRIT_FALSE);
    ASSERT(packed_get(w, 0) == TRIT_FALSE, "idx 0 False");
    ASSERT(w == 0x02ULL, "raw bits: 0b10");
    PASS();
}

static void test_6499(void)
{
    SECTION("Mixed-radix: bin→ternary round-trip 3..27");
    TEST("bin_to_ternary round-trips for 3..27");
    for (unsigned int v = 3; v <= 27; v++)
    {
        trit out[8];
        int len = bin_to_ternary(v, out, 8);
        ASSERT(ternary_to_dec(out, len) == (int)v, "round-trip failed");
    }
    PASS();
}

static void test_6500(void)
{
    SECTION("DOT_TRIT: single element dot");
    TEST("dot_trit single pair T*T=T");
    trit a[1] = {TRIT_TRUE}, b[1] = {TRIT_TRUE};
    /* AND(T,T)=T, OR(F,T)=T */
    ASSERT(dot_trit(a, b, 1) == TRIT_TRUE, "single dot T");
    PASS();
}

static void test_6501(void)
{
    SECTION("Packed64: sanitize all-fault word");
    TEST("Sanitize word with all 0b11 slots → all Unknown (0)");
    uint64_t w = 0xFFFFFFFFFFFFFFFFULL; /* every slot 0b11 = fault */
    uint64_t s = trit_sanitize_packed64(w);
    ASSERT(s == 0ULL, "all faults → all Unknown");
    ASSERT(TRIT_PACKED_VALID(s), "sanitized is valid");
    PASS();
}

int main(void)
{
    printf("=== Batch 114: Tests 6452-6501 — Mixed-Radix & Packed64 SIMD Verification ===\n");
    test_6452();
    test_6453();
    test_6454();
    test_6455();
    test_6456();
    test_6457();
    test_6458();
    test_6459();
    test_6460();
    test_6461();
    test_6462();
    test_6463();
    test_6464();
    test_6465();
    test_6466();
    test_6467();
    test_6468();
    test_6469();
    test_6470();
    test_6471();
    test_6472();
    test_6473();
    test_6474();
    test_6475();
    test_6476();
    test_6477();
    test_6478();
    test_6479();
    test_6480();
    test_6481();
    test_6482();
    test_6483();
    test_6484();
    test_6485();
    test_6486();
    test_6487();
    test_6488();
    test_6489();
    test_6490();
    test_6491();
    test_6492();
    test_6493();
    test_6494();
    test_6495();
    test_6496();
    test_6497();
    test_6498();
    test_6499();
    test_6500();
    test_6501();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return fail_count ? 1 : 0;
}
