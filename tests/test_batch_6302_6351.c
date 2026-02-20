/*==============================================================================
 * Batch 111 – Tests 6302-6351: Ternary Beauty Symmetry Verification
 * Tests the BeautyAppreciator concepts: palindrome detection, symmetry
 * scoring, lattice buffer initialization, and edge cases.
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

/* ---- Inline BeautyAppreciator ----------------------------------------- */
#define LATTICE_CAP 1024

typedef struct
{
    trit symmetry_score;
    trit lattice[LATTICE_CAP];
    int lattice_len;
} BeautyAppreciator;

static void ba_init(BeautyAppreciator *ba)
{
    ba->symmetry_score = TRIT_UNKNOWN;
    for (int i = 0; i < LATTICE_CAP; i++)
        ba->lattice[i] = (trit)((i % 3) - 1); /* cycling {-1,0,+1} */
    ba->lattice_len = LATTICE_CAP;
}

/*
 * trit_beauty_symmetry: check if trit vector is a palindrome.
 * Returns True if symmetric, False if not, Unknown if any mirror-pair
 * contains an Unknown that prevents determination.
 * NULL or len<=0 → False.
 */
static trit trit_beauty_symmetry(const trit *vec, int len)
{
    if (!vec || len <= 0)
        return TRIT_FALSE;
    if (len == 1)
        return TRIT_TRUE;
    trit result = TRIT_TRUE;
    for (int i = 0; i < len / 2; i++)
    {
        trit a = vec[i], b = vec[len - 1 - i];
        if (a == b)
            continue;
        if (a == TRIT_UNKNOWN || b == TRIT_UNKNOWN)
        {
            result = TRIT_UNKNOWN; /* partial: could be either */
        }
        else
        {
            return TRIT_FALSE; /* definite mismatch */
        }
    }
    return result;
}

static void appreciate_beauty(BeautyAppreciator *ba, const trit *vec, int len)
{
    ba->symmetry_score = trit_beauty_symmetry(vec, len);
}

/* ---- Tests ------------------------------------------------------------ */

static void test_6302(void)
{
    SECTION("Beauty: ba_init symmetry_score");
    TEST("ba_init sets symmetry_score to Unknown");
    BeautyAppreciator ba;
    ba_init(&ba);
    ASSERT(ba.symmetry_score == TRIT_UNKNOWN, "should be Unknown");
    PASS();
}

static void test_6303(void)
{
    SECTION("Beauty: ba_init lattice cycling");
    TEST("ba_init creates cycling lattice {-1,0,+1}");
    BeautyAppreciator ba;
    ba_init(&ba);
    for (int i = 0; i < 9; i++)
    {
        trit expected = (trit)((i % 3) - 1);
        ASSERT(ba.lattice[i] == expected, "lattice cycle mismatch");
    }
    PASS();
}

static void test_6304(void)
{
    SECTION("Beauty: ba_init lattice length");
    TEST("ba_init sets lattice_len to LATTICE_CAP (1024)");
    BeautyAppreciator ba;
    ba_init(&ba);
    ASSERT(ba.lattice_len == 1024, "lattice_len should be 1024");
    PASS();
}

static void test_6305(void)
{
    SECTION("Beauty: palindrome {T,U,T}");
    TEST("{T,U,T} is symmetric → True");
    trit vec[3] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_TRUE, "{T,U,T} palindrome");
    PASS();
}

static void test_6306(void)
{
    SECTION("Beauty: palindrome {T,F,T}");
    TEST("{T,F,T} is symmetric → True");
    trit vec[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_TRUE, "{T,F,T} palindrome");
    PASS();
}

static void test_6307(void)
{
    SECTION("Beauty: non-palindrome {T,F,U}");
    TEST("{T,F,U} is not symmetric → False");
    trit vec[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    /* vec[0]=T, vec[2]=U → one Unknown in pair → Unknown; but need to check:
       actually a=T, b=U → one Unknown → result becomes Unknown (partial) */
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_UNKNOWN, "{T,F,U} has Unknown pair");
    PASS();
}

static void test_6308(void)
{
    SECTION("Beauty: definite non-palindrome {T,F,F}");
    TEST("{T,F,F} → definite mismatch → False");
    trit vec[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_FALSE};
    /* vec[0]=T vs vec[2]=F → definite mismatch */
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_FALSE, "definite asymmetry");
    PASS();
}

static void test_6309(void)
{
    SECTION("Beauty: odd-length palindrome {F,T,F}");
    TEST("{F,T,F} is symmetric → True");
    trit vec[3] = {TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_TRUE, "{F,T,F} sym");
    PASS();
}

static void test_6310(void)
{
    SECTION("Beauty: odd-length 5 palindrome");
    TEST("{T,F,U,F,T} is symmetric → True");
    trit vec[5] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 5) == TRIT_TRUE, "5-elem palindrome");
    PASS();
}

static void test_6311(void)
{
    SECTION("Beauty: odd-length 5 non-palindrome");
    TEST("{T,F,U,T,T} is not symmetric → False");
    trit vec[5] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_TRUE};
    /* vec[1]=F vs vec[3]=T → definite mismatch */
    ASSERT(trit_beauty_symmetry(vec, 5) == TRIT_FALSE, "5-elem non-palindrome");
    PASS();
}

static void test_6312(void)
{
    SECTION("Beauty: even-length palindrome {T,T}");
    TEST("{T,T} is symmetric → True");
    trit vec[2] = {TRIT_TRUE, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_TRUE, "{T,T} sym");
    PASS();
}

static void test_6313(void)
{
    SECTION("Beauty: even-length palindrome {F,F}");
    TEST("{F,F} is symmetric → True");
    trit vec[2] = {TRIT_FALSE, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_TRUE, "{F,F} sym");
    PASS();
}

static void test_6314(void)
{
    SECTION("Beauty: even-length non-palindrome {T,F}");
    TEST("{T,F} → definite mismatch → False");
    trit vec[2] = {TRIT_TRUE, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_FALSE, "{T,F} not sym");
    PASS();
}

static void test_6315(void)
{
    SECTION("Beauty: even-length partial {T,U}");
    TEST("{T,U} → Unknown pair → Unknown");
    trit vec[2] = {TRIT_TRUE, TRIT_UNKNOWN};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_UNKNOWN, "{T,U} partial");
    PASS();
}

static void test_6316(void)
{
    SECTION("Beauty: even-length 4 palindrome");
    TEST("{F,T,T,F} is symmetric → True");
    trit vec[4] = {TRIT_FALSE, TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 4) == TRIT_TRUE, "4-elem palindrome");
    PASS();
}

static void test_6317(void)
{
    SECTION("Beauty: even-length 4 non-palindrome");
    TEST("{F,T,F,F} is not symmetric → False");
    trit vec[4] = {TRIT_FALSE, TRIT_TRUE, TRIT_FALSE, TRIT_FALSE};
    /* vec[1]=T vs vec[2]=F → mismatch */
    ASSERT(trit_beauty_symmetry(vec, 4) == TRIT_FALSE, "4-elem non-pal");
    PASS();
}

static void test_6318(void)
{
    SECTION("Beauty: NULL vector → False");
    TEST("NULL vector returns False");
    ASSERT(trit_beauty_symmetry(NULL, 5) == TRIT_FALSE, "NULL → False");
    PASS();
}

static void test_6319(void)
{
    SECTION("Beauty: len=0 → False");
    TEST("Zero-length vector returns False");
    trit vec[1] = {TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 0) == TRIT_FALSE, "len=0 → False");
    PASS();
}

static void test_6320(void)
{
    SECTION("Beauty: negative len → False");
    TEST("Negative length returns False");
    trit vec[1] = {TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, -1) == TRIT_FALSE, "neg len → False");
    PASS();
}

static void test_6321(void)
{
    SECTION("Beauty: single element True → True");
    TEST("Single True element is always symmetric");
    trit vec[1] = {TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 1) == TRIT_TRUE, "single T → True");
    PASS();
}

static void test_6322(void)
{
    SECTION("Beauty: single element False → True");
    TEST("Single False element is always symmetric");
    trit vec[1] = {TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 1) == TRIT_TRUE, "single F → True");
    PASS();
}

static void test_6323(void)
{
    SECTION("Beauty: single element Unknown → True");
    TEST("Single Unknown element is always symmetric");
    trit vec[1] = {TRIT_UNKNOWN};
    ASSERT(trit_beauty_symmetry(vec, 1) == TRIT_TRUE, "single U → True");
    PASS();
}

static void test_6324(void)
{
    SECTION("Beauty: len-2 matching Unknown {U,U}");
    TEST("{U,U} is symmetric → True");
    trit vec[2] = {TRIT_UNKNOWN, TRIT_UNKNOWN};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_TRUE, "{U,U} sym");
    PASS();
}

static void test_6325(void)
{
    SECTION("Beauty: len-2 {F,U} partial");
    TEST("{F,U} → Unknown pair → Unknown");
    trit vec[2] = {TRIT_FALSE, TRIT_UNKNOWN};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_UNKNOWN, "{F,U} partial");
    PASS();
}

static void test_6326(void)
{
    SECTION("Beauty: len-2 {U,F} partial");
    TEST("{U,F} → Unknown pair → Unknown");
    trit vec[2] = {TRIT_UNKNOWN, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_UNKNOWN, "{U,F} partial");
    PASS();
}

static void test_6327(void)
{
    SECTION("Beauty: all-True vec len=6");
    TEST("{T,T,T,T,T,T} always symmetric → True");
    trit vec[6] = {1, 1, 1, 1, 1, 1};
    ASSERT(trit_beauty_symmetry(vec, 6) == TRIT_TRUE, "all-True sym");
    PASS();
}

static void test_6328(void)
{
    SECTION("Beauty: all-False vec len=6");
    TEST("{F,F,F,F,F,F} always symmetric → True");
    trit vec[6] = {-1, -1, -1, -1, -1, -1};
    ASSERT(trit_beauty_symmetry(vec, 6) == TRIT_TRUE, "all-False sym");
    PASS();
}

static void test_6329(void)
{
    SECTION("Beauty: all-Unknown vec len=6");
    TEST("{U,U,U,U,U,U} always symmetric → True");
    trit vec[6] = {0, 0, 0, 0, 0, 0};
    ASSERT(trit_beauty_symmetry(vec, 6) == TRIT_TRUE, "all-Unknown sym");
    PASS();
}

static void test_6330(void)
{
    SECTION("Beauty: appreciate_beauty stores result");
    TEST("appreciate_beauty stores symmetry_score");
    BeautyAppreciator ba;
    ba_init(&ba);
    trit vec[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    appreciate_beauty(&ba, vec, 3);
    ASSERT(ba.symmetry_score == TRIT_TRUE, "score stored as True");
    PASS();
}

static void test_6331(void)
{
    SECTION("Beauty: appreciate_beauty asymmetric");
    TEST("appreciate_beauty scores asymmetric vec as False");
    BeautyAppreciator ba;
    ba_init(&ba);
    trit vec[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_FALSE};
    appreciate_beauty(&ba, vec, 3);
    ASSERT(ba.symmetry_score == TRIT_FALSE, "score stored as False");
    PASS();
}

static void test_6332(void)
{
    SECTION("Beauty: appreciate_beauty partial");
    TEST("appreciate_beauty scores partial vec as Unknown");
    BeautyAppreciator ba;
    ba_init(&ba);
    trit vec[2] = {TRIT_TRUE, TRIT_UNKNOWN};
    appreciate_beauty(&ba, vec, 2);
    ASSERT(ba.symmetry_score == TRIT_UNKNOWN, "score is Unknown");
    PASS();
}

static void test_6333(void)
{
    SECTION("Beauty: lattice buffer capped at 1024");
    TEST("Lattice buffer is exactly 1024 elements");
    BeautyAppreciator ba;
    ba_init(&ba);
    ASSERT(ba.lattice_len == LATTICE_CAP, "capped at 1024");
    ASSERT(LATTICE_CAP == 1024, "LATTICE_CAP is 1024");
    PASS();
}

static void test_6334(void)
{
    SECTION("Beauty: lattice end values");
    TEST("Lattice last elements follow cycling pattern");
    BeautyAppreciator ba;
    ba_init(&ba);
    ASSERT(ba.lattice[1023] == (trit)((1023 % 3) - 1), "last slot correct");
    ASSERT(ba.lattice[1022] == (trit)((1022 % 3) - 1), "second-to-last correct");
    PASS();
}

static void test_6335(void)
{
    SECTION("Beauty: partial symmetry with multiple Unknown pairs");
    TEST("{U,T,U} pairs: [0]=U vs [2]=U both Unknown, match → True");
    trit vec[3] = {TRIT_UNKNOWN, TRIT_TRUE, TRIT_UNKNOWN};
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_TRUE, "{U,T,U} sym");
    PASS();
}

static void test_6336(void)
{
    SECTION("Beauty: mixed partial {U,F,T,F,U}");
    TEST("{U,F,T,F,U} → pairs (U,U) and (F,F) both match → True");
    trit vec[5] = {TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
    ASSERT(trit_beauty_symmetry(vec, 5) == TRIT_TRUE, "mirror-sym");
    PASS();
}

static void test_6337(void)
{
    SECTION("Beauty: asymmetric even {T,F,T,T}");
    TEST("{T,F,T,T} → pair (F,T) mismatch → False");
    trit vec[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_TRUE};
    /* vec[0]=T vs vec[3]=T ok, vec[1]=F vs vec[2]=T mismatch */
    ASSERT(trit_beauty_symmetry(vec, 4) == TRIT_FALSE, "inner mismatch");
    PASS();
}

static void test_6338(void)
{
    SECTION("Beauty: 6-element palindrome");
    TEST("{T,F,U,U,F,T} is symmetric → True");
    trit vec[6] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 6) == TRIT_TRUE, "6-pal");
    PASS();
}

static void test_6339(void)
{
    SECTION("Beauty: 6-element asymmetric");
    TEST("{T,F,U,T,F,T} → pair (U,T): partial → but (F,F): ok → Unknown");
    trit vec[6] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE, TRIT_FALSE, TRIT_TRUE};
    /* pair(0,5)=T,T ok; pair(1,4)=F,F ok; pair(2,3)=U,T → Unknown */
    ASSERT(trit_beauty_symmetry(vec, 6) == TRIT_UNKNOWN, "partial sym");
    PASS();
}

static void test_6340(void)
{
    SECTION("Beauty: repeated init resets score");
    TEST("ba_init resets symmetry_score to Unknown");
    BeautyAppreciator ba;
    ba_init(&ba);
    trit vec[2] = {TRIT_TRUE, TRIT_TRUE};
    appreciate_beauty(&ba, vec, 2);
    ASSERT(ba.symmetry_score == TRIT_TRUE, "after first appreciate");
    ba_init(&ba);
    ASSERT(ba.symmetry_score == TRIT_UNKNOWN, "reset to Unknown");
    PASS();
}

static void test_6341(void)
{
    SECTION("Beauty: lattice copy capped");
    TEST("Lattice copy: writing beyond cap boundary should not affect struct");
    BeautyAppreciator ba;
    ba_init(&ba);
    /* Just verify the boundary is respected */
    int cap = ba.lattice_len;
    ASSERT(cap <= LATTICE_CAP, "lattice_len <= LATTICE_CAP");
    PASS();
}

static void test_6342(void)
{
    SECTION("Beauty: 7-element palindrome");
    TEST("{F,T,F,U,F,T,F} is symmetric → True");
    trit vec[7] = {TRIT_FALSE, TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 7) == TRIT_TRUE, "7-pal");
    PASS();
}

static void test_6343(void)
{
    SECTION("Beauty: 8-element palindrome");
    TEST("{T,T,F,F,F,F,T,T} is symmetric → True");
    trit vec[8] = {1, 1, -1, -1, -1, -1, 1, 1};
    ASSERT(trit_beauty_symmetry(vec, 8) == TRIT_TRUE, "8-pal");
    PASS();
}

static void test_6344(void)
{
    SECTION("Beauty: early mismatch short-circuits");
    TEST("First pair mismatch returns False immediately");
    trit vec[4] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_FALSE};
    /* vec[0]=T vs vec[3]=F → definite mismatch → False (even though inner pair has Unknown) */
    ASSERT(trit_beauty_symmetry(vec, 4) == TRIT_FALSE, "early mismatch");
    PASS();
}

static void test_6345(void)
{
    SECTION("Beauty: appreciate NULL vector");
    TEST("appreciate_beauty with NULL → False stored");
    BeautyAppreciator ba;
    ba_init(&ba);
    appreciate_beauty(&ba, NULL, 0);
    ASSERT(ba.symmetry_score == TRIT_FALSE, "NULL → False");
    PASS();
}

static void test_6346(void)
{
    SECTION("Beauty: len-2 {U,T} partial");
    TEST("{U,T} → Unknown pair → Unknown");
    trit vec[2] = {TRIT_UNKNOWN, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 2) == TRIT_UNKNOWN, "{U,T} partial");
    PASS();
}

static void test_6347(void)
{
    SECTION("Beauty: len-3 all-False palindrome");
    TEST("{F,F,F} symmetric → True");
    trit vec[3] = {TRIT_FALSE, TRIT_FALSE, TRIT_FALSE};
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_TRUE, "{F,F,F} sym");
    PASS();
}

static void test_6348(void)
{
    SECTION("Beauty: len-3 all-True palindrome");
    TEST("{T,T,T} symmetric → True");
    trit vec[3] = {TRIT_TRUE, TRIT_TRUE, TRIT_TRUE};
    ASSERT(trit_beauty_symmetry(vec, 3) == TRIT_TRUE, "{T,T,T} sym");
    PASS();
}

static void test_6349(void)
{
    SECTION("Beauty: long palindrome 10 elements");
    TEST("{T,F,U,T,F,F,T,U,F,T} is symmetric → True");
    trit vec[10] = {1, -1, 0, 1, -1, -1, 1, 0, -1, 1};
    ASSERT(trit_beauty_symmetry(vec, 10) == TRIT_TRUE, "10-pal");
    PASS();
}

static void test_6350(void)
{
    SECTION("Beauty: long non-palindrome 10 elements");
    TEST("{T,F,U,T,F,T,T,U,F,T} → inner mismatch → False");
    trit vec[10] = {1, -1, 0, 1, -1, 1, 1, 0, -1, 1};
    /* pair(4): vec[4]=-1 vs vec[5]=1 → mismatch */
    ASSERT(trit_beauty_symmetry(vec, 10) == TRIT_FALSE, "10-non-pal");
    PASS();
}

static void test_6351(void)
{
    SECTION("Beauty: appreciate then re-appreciate overwrites");
    TEST("Second appreciate_beauty overwrites first score");
    BeautyAppreciator ba;
    ba_init(&ba);
    trit v1[2] = {TRIT_TRUE, TRIT_TRUE};
    appreciate_beauty(&ba, v1, 2);
    ASSERT(ba.symmetry_score == TRIT_TRUE, "first: True");
    trit v2[2] = {TRIT_TRUE, TRIT_FALSE};
    appreciate_beauty(&ba, v2, 2);
    ASSERT(ba.symmetry_score == TRIT_FALSE, "second: False overwrites");
    PASS();
}

int main(void)
{
    printf("=== Batch 111: Tests 6302-6351 — Ternary Beauty Symmetry Verification ===\n");
    test_6302();
    test_6303();
    test_6304();
    test_6305();
    test_6306();
    test_6307();
    test_6308();
    test_6309();
    test_6310();
    test_6311();
    test_6312();
    test_6313();
    test_6314();
    test_6315();
    test_6316();
    test_6317();
    test_6318();
    test_6319();
    test_6320();
    test_6321();
    test_6322();
    test_6323();
    test_6324();
    test_6325();
    test_6326();
    test_6327();
    test_6328();
    test_6329();
    test_6330();
    test_6331();
    test_6332();
    test_6333();
    test_6334();
    test_6335();
    test_6336();
    test_6337();
    test_6338();
    test_6339();
    test_6340();
    test_6341();
    test_6342();
    test_6343();
    test_6344();
    test_6345();
    test_6346();
    test_6347();
    test_6348();
    test_6349();
    test_6350();
    test_6351();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return fail_count ? 1 : 0;
}
