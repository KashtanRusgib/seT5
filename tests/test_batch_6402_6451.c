/*==============================================================================
 * Batch 113 – Tests 6402-6451: Balanced Ternary Arithmetic Edge Cases
 * Tests fundamental balanced ternary encode/decode, round-trip, addition,
 * multiplication, negation, comparison, and boundary cases.
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

/* ---- Inline Balanced Ternary Arithmetic ------------------------------- */
#define BT_MAX_TRITS 8 /* supports up to 3^8-1/2 = 3280 */

typedef struct
{
    trit digits[BT_MAX_TRITS]; /* LSB first: digits[0] is 3^0 */
    int len;                   /* number of significant trits */
} BalancedTernary;

/* Encode int → balanced ternary */
static BalancedTernary bt_encode(int val)
{
    BalancedTernary bt;
    memset(&bt, 0, sizeof(bt));
    if (val == 0)
    {
        bt.digits[0] = 0;
        bt.len = 1;
        return bt;
    }
    int neg = (val < 0);
    int v = neg ? -val : val;
    int i = 0;
    while (v > 0 && i < BT_MAX_TRITS)
    {
        int rem = v % 3;
        if (rem == 2)
        {
            bt.digits[i] = -1;
            v = (v + 1) / 3;
        }
        else if (rem == 0)
        {
            bt.digits[i] = 0;
            v = v / 3;
        }
        else
        {
            bt.digits[i] = 1;
            v = v / 3;
        }
        i++;
    }
    bt.len = i;
    if (neg)
    {
        for (int j = 0; j < bt.len; j++)
            bt.digits[j] = (trit)(-bt.digits[j]);
    }
    return bt;
}

/* Decode balanced ternary → int */
static int bt_decode(const BalancedTernary *bt)
{
    int val = 0, pw = 1;
    for (int i = 0; i < bt->len; i++)
    {
        val += bt->digits[i] * pw;
        pw *= 3;
    }
    return val;
}

/* Negate: flip all trits */
static BalancedTernary bt_negate(const BalancedTernary *bt)
{
    BalancedTernary neg;
    neg.len = bt->len;
    for (int i = 0; i < bt->len; i++)
        neg.digits[i] = (trit)(-bt->digits[i]);
    for (int i = bt->len; i < BT_MAX_TRITS; i++)
        neg.digits[i] = 0;
    return neg;
}

/* Add two balanced ternary values (via int) */
static BalancedTernary bt_add(const BalancedTernary *a, const BalancedTernary *b)
{
    return bt_encode(bt_decode(a) + bt_decode(b));
}

/* Multiply two balanced ternary values (via int) */
static BalancedTernary bt_mul(const BalancedTernary *a, const BalancedTernary *b)
{
    return bt_encode(bt_decode(a) * bt_decode(b));
}

/* Compare: returns -1, 0, or +1 */
static int bt_compare(const BalancedTernary *a, const BalancedTernary *b)
{
    int va = bt_decode(a), vb = bt_decode(b);
    if (va < vb)
        return -1;
    if (va > vb)
        return 1;
    return 0;
}

/* ---- Tests ------------------------------------------------------------ */

static void test_6402(void)
{
    SECTION("BT Encode: 0");
    TEST("bt_encode(0) → [0], len=1");
    BalancedTernary bt = bt_encode(0);
    ASSERT(bt.len == 1, "len=1");
    ASSERT(bt.digits[0] == 0, "digit[0]=0");
    PASS();
}

static void test_6403(void)
{
    SECTION("BT Encode: 1");
    TEST("bt_encode(1) → [+1], len=1");
    BalancedTernary bt = bt_encode(1);
    ASSERT(bt.len == 1, "len=1");
    ASSERT(bt.digits[0] == 1, "digit[0]=+1");
    PASS();
}

static void test_6404(void)
{
    SECTION("BT Encode: -1");
    TEST("bt_encode(-1) → [-1], len=1");
    BalancedTernary bt = bt_encode(-1);
    ASSERT(bt.len == 1, "len=1");
    ASSERT(bt.digits[0] == -1, "digit[0]=-1");
    PASS();
}

static void test_6405(void)
{
    SECTION("BT Encode: 2");
    TEST("bt_encode(2) → [+1,-1] (1*1 + (-1)*3 = -2? No: LSB first: d[0]*1 + d[1]*3)");
    /* 2 = 1*1 + 1*3 - 1*3? Let's just decode and check. 2%3=2 → d[0]=-1, v=(2+1)/3=1
       1%3=1 → d[1]=+1, v=0. So [-1, +1]: -1*1 + 1*3 = 2. ✓ */
    BalancedTernary bt = bt_encode(2);
    ASSERT(bt.len == 2, "len=2");
    ASSERT(bt.digits[0] == -1, "d[0]=-1");
    ASSERT(bt.digits[1] == 1, "d[1]=+1");
    PASS();
}

static void test_6406(void)
{
    SECTION("BT Encode: 3");
    TEST("bt_encode(3) → [0,+1]: 0*1+1*3=3");
    BalancedTernary bt = bt_encode(3);
    ASSERT(bt.len == 2, "len=2");
    ASSERT(bt.digits[0] == 0, "d[0]=0");
    ASSERT(bt.digits[1] == 1, "d[1]=+1");
    PASS();
}

static void test_6407(void)
{
    SECTION("BT Encode: 13");
    TEST("bt_encode(13) → [+1,+1,+1]: 1+3+9=13");
    BalancedTernary bt = bt_encode(13);
    ASSERT(bt.len == 3, "len=3");
    ASSERT(bt.digits[0] == 1, "d[0]=+1");
    ASSERT(bt.digits[1] == 1, "d[1]=+1");
    ASSERT(bt.digits[2] == 1, "d[2]=+1");
    PASS();
}

static void test_6408(void)
{
    SECTION("BT Decode: [+1,+1,+1]");
    TEST("decode([+1,+1,+1]) == 13");
    BalancedTernary bt = bt_encode(13);
    ASSERT(bt_decode(&bt) == 13, "decode==13");
    PASS();
}

static void test_6409(void)
{
    SECTION("BT Decode: [0]");
    TEST("decode([0]) == 0");
    BalancedTernary bt = bt_encode(0);
    ASSERT(bt_decode(&bt) == 0, "decode==0");
    PASS();
}

static void test_6410(void)
{
    SECTION("BT Round-trip: -40 to -21");
    TEST("Encode→decode round-trip for -40..-21");
    for (int v = -40; v <= -21; v++)
    {
        BalancedTernary bt = bt_encode(v);
        ASSERT(bt_decode(&bt) == v, "round-trip failed");
    }
    PASS();
}

static void test_6411(void)
{
    SECTION("BT Round-trip: -20 to -1");
    TEST("Encode→decode round-trip for -20..-1");
    for (int v = -20; v <= -1; v++)
    {
        BalancedTernary bt = bt_encode(v);
        ASSERT(bt_decode(&bt) == v, "round-trip failed");
    }
    PASS();
}

static void test_6412(void)
{
    SECTION("BT Round-trip: 0 to 20");
    TEST("Encode→decode round-trip for 0..20");
    for (int v = 0; v <= 20; v++)
    {
        BalancedTernary bt = bt_encode(v);
        ASSERT(bt_decode(&bt) == v, "round-trip failed");
    }
    PASS();
}

static void test_6413(void)
{
    SECTION("BT Round-trip: 21 to 40");
    TEST("Encode→decode round-trip for 21..40");
    for (int v = 21; v <= 40; v++)
    {
        BalancedTernary bt = bt_encode(v);
        ASSERT(bt_decode(&bt) == v, "round-trip failed");
    }
    PASS();
}

static void test_6414(void)
{
    SECTION("BT Addition: 1+1=2");
    TEST("bt_add(1,1) decodes to 2");
    BalancedTernary a = bt_encode(1), b = bt_encode(1);
    BalancedTernary sum = bt_add(&a, &b);
    ASSERT(bt_decode(&sum) == 2, "1+1=2");
    PASS();
}

static void test_6415(void)
{
    SECTION("BT Addition: 13+(-13)=0");
    TEST("bt_add(13,-13) decodes to 0");
    BalancedTernary a = bt_encode(13), b = bt_encode(-13);
    BalancedTernary sum = bt_add(&a, &b);
    ASSERT(bt_decode(&sum) == 0, "13+(-13)=0");
    PASS();
}

static void test_6416(void)
{
    SECTION("BT Addition: -5+8=3");
    TEST("bt_add(-5,8) decodes to 3");
    BalancedTernary a = bt_encode(-5), b = bt_encode(8);
    BalancedTernary sum = bt_add(&a, &b);
    ASSERT(bt_decode(&sum) == 3, "-5+8=3");
    PASS();
}

static void test_6417(void)
{
    SECTION("BT Addition: 0+0=0");
    TEST("bt_add(0,0) decodes to 0");
    BalancedTernary a = bt_encode(0), b = bt_encode(0);
    BalancedTernary sum = bt_add(&a, &b);
    ASSERT(bt_decode(&sum) == 0, "0+0=0");
    PASS();
}

static void test_6418(void)
{
    SECTION("BT Multiplication: 3*3=9");
    TEST("bt_mul(3,3) decodes to 9");
    BalancedTernary a = bt_encode(3), b = bt_encode(3);
    BalancedTernary prod = bt_mul(&a, &b);
    ASSERT(bt_decode(&prod) == 9, "3*3=9");
    PASS();
}

static void test_6419(void)
{
    SECTION("BT Multiplication: -2*5=-10");
    TEST("bt_mul(-2,5) decodes to -10");
    BalancedTernary a = bt_encode(-2), b = bt_encode(5);
    BalancedTernary prod = bt_mul(&a, &b);
    ASSERT(bt_decode(&prod) == -10, "-2*5=-10");
    PASS();
}

static void test_6420(void)
{
    SECTION("BT Multiplication: 0*100=0");
    TEST("bt_mul(0,100) decodes to 0");
    BalancedTernary a = bt_encode(0), b = bt_encode(100);
    BalancedTernary prod = bt_mul(&a, &b);
    ASSERT(bt_decode(&prod) == 0, "0*100=0");
    PASS();
}

static void test_6421(void)
{
    SECTION("BT Multiplication: 1*(-1)=-1");
    TEST("bt_mul(1,-1) decodes to -1");
    BalancedTernary a = bt_encode(1), b = bt_encode(-1);
    BalancedTernary prod = bt_mul(&a, &b);
    ASSERT(bt_decode(&prod) == -1, "1*(-1)=-1");
    PASS();
}

static void test_6422(void)
{
    SECTION("BT Negation: neg(13)=-13");
    TEST("bt_negate(13) decodes to -13");
    BalancedTernary bt = bt_encode(13);
    BalancedTernary neg = bt_negate(&bt);
    ASSERT(bt_decode(&neg) == -13, "neg(13)=-13");
    PASS();
}

static void test_6423(void)
{
    SECTION("BT Negation: neg(0)=0");
    TEST("bt_negate(0) decodes to 0");
    BalancedTernary bt = bt_encode(0);
    BalancedTernary neg = bt_negate(&bt);
    ASSERT(bt_decode(&neg) == 0, "neg(0)=0");
    PASS();
}

static void test_6424(void)
{
    SECTION("BT Negation: neg(neg(x))=x");
    TEST("Double negation of 7 returns 7");
    BalancedTernary bt = bt_encode(7);
    BalancedTernary n1 = bt_negate(&bt);
    BalancedTernary n2 = bt_negate(&n1);
    ASSERT(bt_decode(&n2) == 7, "neg(neg(7))=7");
    PASS();
}

static void test_6425(void)
{
    SECTION("BT Negation: neg flips all trits");
    TEST("Each trit in neg(13) is negated");
    BalancedTernary bt = bt_encode(13);
    BalancedTernary neg = bt_negate(&bt);
    for (int i = 0; i < bt.len; i++)
        ASSERT(neg.digits[i] == -bt.digits[i], "trit flip");
    PASS();
}

static void test_6426(void)
{
    SECTION("BT Compare: 5 < 10");
    TEST("bt_compare(5,10) == -1");
    BalancedTernary a = bt_encode(5), b = bt_encode(10);
    ASSERT(bt_compare(&a, &b) == -1, "5<10");
    PASS();
}

static void test_6427(void)
{
    SECTION("BT Compare: 10 > 5");
    TEST("bt_compare(10,5) == 1");
    BalancedTernary a = bt_encode(10), b = bt_encode(5);
    ASSERT(bt_compare(&a, &b) == 1, "10>5");
    PASS();
}

static void test_6428(void)
{
    SECTION("BT Compare: 7 == 7");
    TEST("bt_compare(7,7) == 0");
    BalancedTernary a = bt_encode(7), b = bt_encode(7);
    ASSERT(bt_compare(&a, &b) == 0, "7==7");
    PASS();
}

static void test_6429(void)
{
    SECTION("BT Compare: -3 < 3");
    TEST("bt_compare(-3,3) == -1");
    BalancedTernary a = bt_encode(-3), b = bt_encode(3);
    ASSERT(bt_compare(&a, &b) == -1, "-3<3");
    PASS();
}

static void test_6430(void)
{
    SECTION("BT Compare: 0 == 0");
    TEST("bt_compare(0,0) == 0");
    BalancedTernary a = bt_encode(0), b = bt_encode(0);
    ASSERT(bt_compare(&a, &b) == 0, "0==0");
    PASS();
}

static void test_6431(void)
{
    SECTION("BT Encode: -2");
    TEST("bt_encode(-2) → [+1,-1] but negated: [1,-1]? decode check");
    BalancedTernary bt = bt_encode(-2);
    ASSERT(bt_decode(&bt) == -2, "decode==-2");
    PASS();
}

static void test_6432(void)
{
    SECTION("BT Encode: -3");
    TEST("bt_encode(-3) decodes to -3");
    BalancedTernary bt = bt_encode(-3);
    ASSERT(bt_decode(&bt) == -3, "decode==-3");
    PASS();
}

static void test_6433(void)
{
    SECTION("BT Encode: -13");
    TEST("bt_encode(-13) → negated [+1,+1,+1] = [-1,-1,-1]");
    BalancedTernary bt = bt_encode(-13);
    ASSERT(bt.len == 3, "len=3");
    ASSERT(bt.digits[0] == -1, "d[0]=-1");
    ASSERT(bt.digits[1] == -1, "d[1]=-1");
    ASSERT(bt.digits[2] == -1, "d[2]=-1");
    ASSERT(bt_decode(&bt) == -13, "decode==-13");
    PASS();
}

static void test_6434(void)
{
    SECTION("BT Large: 243 = 3^5");
    TEST("bt_encode(243) round-trip");
    BalancedTernary bt = bt_encode(243);
    ASSERT(bt_decode(&bt) == 243, "243 round-trip");
    PASS();
}

static void test_6435(void)
{
    SECTION("BT Large: -243");
    TEST("bt_encode(-243) round-trip");
    BalancedTernary bt = bt_encode(-243);
    ASSERT(bt_decode(&bt) == -243, "-243 round-trip");
    PASS();
}

static void test_6436(void)
{
    SECTION("BT Large: 121 = (3^5-1)/2");
    TEST("bt_encode(121) round-trip");
    BalancedTernary bt = bt_encode(121);
    ASSERT(bt_decode(&bt) == 121, "121 round-trip");
    PASS();
}

static void test_6437(void)
{
    SECTION("BT Large: 100");
    TEST("bt_encode(100) round-trip");
    BalancedTernary bt = bt_encode(100);
    ASSERT(bt_decode(&bt) == 100, "100 round-trip");
    PASS();
}

static void test_6438(void)
{
    SECTION("BT Large: 200");
    TEST("bt_encode(200) round-trip");
    BalancedTernary bt = bt_encode(200);
    ASSERT(bt_decode(&bt) == 200, "200 round-trip");
    PASS();
}

static void test_6439(void)
{
    SECTION("BT Addition: -40+40=0");
    TEST("bt_add(-40,40) == 0");
    BalancedTernary a = bt_encode(-40), b = bt_encode(40);
    BalancedTernary sum = bt_add(&a, &b);
    ASSERT(bt_decode(&sum) == 0, "-40+40=0");
    PASS();
}

static void test_6440(void)
{
    SECTION("BT Addition: 20+21=41");
    TEST("bt_add(20,21) == 41");
    BalancedTernary a = bt_encode(20), b = bt_encode(21);
    BalancedTernary sum = bt_add(&a, &b);
    ASSERT(bt_decode(&sum) == 41, "20+21=41");
    PASS();
}

static void test_6441(void)
{
    SECTION("BT Multiplication: -1*-1=1");
    TEST("bt_mul(-1,-1) == 1");
    BalancedTernary a = bt_encode(-1), b = bt_encode(-1);
    BalancedTernary prod = bt_mul(&a, &b);
    ASSERT(bt_decode(&prod) == 1, "-1*-1=1");
    PASS();
}

static void test_6442(void)
{
    SECTION("BT Multiplication: 13*1=13");
    TEST("bt_mul(13,1) == 13");
    BalancedTernary a = bt_encode(13), b = bt_encode(1);
    BalancedTernary prod = bt_mul(&a, &b);
    ASSERT(bt_decode(&prod) == 13, "13*1=13");
    PASS();
}

static void test_6443(void)
{
    SECTION("BT Encode: 4");
    TEST("bt_encode(4) → 4=1*1+1*3 → [+1,+1]");
    BalancedTernary bt = bt_encode(4);
    ASSERT(bt_decode(&bt) == 4, "decode==4");
    /* 4: 4%3=1 → d[0]=1, v=1; 1%3=1 → d[1]=1, v=0 → [1,1] = 1+3 = 4 ✓ */
    ASSERT(bt.digits[0] == 1, "d[0]=1");
    ASSERT(bt.digits[1] == 1, "d[1]=1");
    PASS();
}

static void test_6444(void)
{
    SECTION("BT Encode: 5");
    TEST("bt_encode(5) round-trip");
    BalancedTernary bt = bt_encode(5);
    ASSERT(bt_decode(&bt) == 5, "decode==5");
    /* 5: 5%3=2→d[0]=-1,v=2; 2%3=2→d[1]=-1,v=1; 1%3=1→d[2]=1 → [-1,-1,1] = -1-3+9 = 5 ✓ */
    PASS();
}

static void test_6445(void)
{
    SECTION("BT Encode: 6");
    TEST("bt_encode(6) round-trip");
    BalancedTernary bt = bt_encode(6);
    ASSERT(bt_decode(&bt) == 6, "decode==6");
    PASS();
}

static void test_6446(void)
{
    SECTION("BT Encode: 7");
    TEST("bt_encode(7) round-trip");
    BalancedTernary bt = bt_encode(7);
    ASSERT(bt_decode(&bt) == 7, "decode==7");
    PASS();
}

static void test_6447(void)
{
    SECTION("BT Encode: 8");
    TEST("bt_encode(8) round-trip");
    BalancedTernary bt = bt_encode(8);
    ASSERT(bt_decode(&bt) == 8, "decode==8");
    PASS();
}

static void test_6448(void)
{
    SECTION("BT Encode: 9 (3^2)");
    TEST("bt_encode(9) → [0,0,+1]: 9");
    BalancedTernary bt = bt_encode(9);
    ASSERT(bt_decode(&bt) == 9, "decode==9");
    ASSERT(bt.digits[0] == 0, "d[0]=0");
    ASSERT(bt.digits[1] == 0, "d[1]=0");
    ASSERT(bt.digits[2] == 1, "d[2]=1");
    PASS();
}

static void test_6449(void)
{
    SECTION("BT Encode: 27 (3^3)");
    TEST("bt_encode(27) → [0,0,0,+1]: 27");
    BalancedTernary bt = bt_encode(27);
    ASSERT(bt_decode(&bt) == 27, "decode==27");
    ASSERT(bt.digits[0] == 0, "d[0]=0");
    ASSERT(bt.digits[1] == 0, "d[1]=0");
    ASSERT(bt.digits[2] == 0, "d[2]=0");
    ASSERT(bt.digits[3] == 1, "d[3]=1");
    PASS();
}

static void test_6450(void)
{
    SECTION("BT Encode: 81 (3^4)");
    TEST("bt_encode(81) round-trip");
    BalancedTernary bt = bt_encode(81);
    ASSERT(bt_decode(&bt) == 81, "decode==81");
    PASS();
}

static void test_6451(void)
{
    SECTION("BT Boundary: encode large then negate");
    TEST("bt_negate(bt_encode(200)) decodes to -200");
    BalancedTernary bt = bt_encode(200);
    BalancedTernary neg = bt_negate(&bt);
    ASSERT(bt_decode(&neg) == -200, "neg(200)==-200");
    PASS();
}

int main(void)
{
    printf("=== Batch 113: Tests 6402-6451 — Balanced Ternary Arithmetic Edge Cases ===\n");
    test_6402();
    test_6403();
    test_6404();
    test_6405();
    test_6406();
    test_6407();
    test_6408();
    test_6409();
    test_6410();
    test_6411();
    test_6412();
    test_6413();
    test_6414();
    test_6415();
    test_6416();
    test_6417();
    test_6418();
    test_6419();
    test_6420();
    test_6421();
    test_6422();
    test_6423();
    test_6424();
    test_6425();
    test_6426();
    test_6427();
    test_6428();
    test_6429();
    test_6430();
    test_6431();
    test_6432();
    test_6433();
    test_6434();
    test_6435();
    test_6436();
    test_6437();
    test_6438();
    test_6439();
    test_6440();
    test_6441();
    test_6442();
    test_6443();
    test_6444();
    test_6445();
    test_6446();
    test_6447();
    test_6448();
    test_6449();
    test_6450();
    test_6451();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return fail_count ? 1 : 0;
}
