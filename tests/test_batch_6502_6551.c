/*==============================================================================
 * Batch 115 – Tests 6502-6551: Heptavint Multi-Radix Encoding
 * Tests balanced base-7 (heptavint) encoding using trits: 2 trits represent
 * values -3..+3 in balanced base-7, plus radix conversion and overflow.
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

/* ---- Heptavint representation: 2 trits encode balanced base-7 digit ---- */
/* A heptavint digit represents values -3..+3 (7 values, balanced around 0). */
/* Encoding: value = hi * 3 + lo, where hi and lo are trits (-1,0,+1).      */
/* This gives range -4..+4 (9 values), but we clamp to -3..+3 for base-7.   */

typedef struct
{
    trit hi; /* high trit */
    trit lo; /* low trit  */
} heptavint_t;

/* Encode integer -3..+3 into heptavint (2-trit balanced representation) */
static int heptavint_encode(int value, heptavint_t *out)
{
    if (value < -3 || value > 3)
        return -1; /* overflow */
    /* balanced ternary decomposition: value = hi*3 + lo, lo in {-1,0,1} */
    int lo = value % 3;
    int hi = value / 3;
    /* Fix: C modulo can give negative lo for negative values */
    if (lo > 1)
    {
        lo -= 3;
        hi += 1;
    }
    if (lo < -1)
    {
        lo += 3;
        hi -= 1;
    }
    out->hi = (trit)hi;
    out->lo = (trit)lo;
    return 0;
}

/* Decode heptavint back to integer */
static int heptavint_decode(const heptavint_t *hv)
{
    return hv->hi * 3 + hv->lo;
}

/* Check if heptavint value is in valid range -3..+3 */
static int heptavint_valid(const heptavint_t *hv)
{
    int v = hv->hi * 3 + hv->lo;
    return (v >= -3 && v <= 3);
}

/* Add two heptavint digits, return 0 on success, -1 on overflow */
static int heptavint_add(const heptavint_t *a, const heptavint_t *b, heptavint_t *result)
{
    int sum = heptavint_decode(a) + heptavint_decode(b);
    if (sum < -3 || sum > 3)
        return -1; /* overflow */
    return heptavint_encode(sum, result);
}

/* Check if heptavint is zero */
static int heptavint_is_zero(const heptavint_t *hv)
{
    return (hv->hi == 0 && hv->lo == 0);
}

/* Negate a heptavint digit */
static void heptavint_negate(const heptavint_t *in, heptavint_t *out)
{
    out->hi = (trit)(-in->hi);
    out->lo = (trit)(-in->lo);
}

/* Convert a balanced ternary 2-trit value to an integer */
static int base3_decode(trit hi, trit lo)
{
    return hi * 3 + lo;
}

/* Convert integer to balanced ternary 2-trit (same as heptavint for range) */
static void base3_encode(int val, trit *hi, trit *lo)
{
    int l = val % 3;
    int h = val / 3;
    if (l > 1)
    {
        l -= 3;
        h += 1;
    }
    if (l < -1)
    {
        l += 3;
        h -= 1;
    }
    *hi = (trit)h;
    *lo = (trit)l;
}

/* Heptavint vector: array of heptavint digits */
typedef struct
{
    heptavint_t digits[4];
    int len;
} heptavint_vec_t;

/* Pack integer array into heptavint vector */
static int heptavint_vec_pack(const int *values, int n, heptavint_vec_t *vec)
{
    if (n > 4)
        return -1;
    vec->len = n;
    for (int i = 0; i < n; i++)
    {
        if (heptavint_encode(values[i], &vec->digits[i]) != 0)
            return -1;
    }
    return 0;
}

/* Unpack heptavint vector to integer array */
static void heptavint_vec_unpack(const heptavint_vec_t *vec, int *values)
{
    for (int i = 0; i < vec->len; i++)
    {
        values[i] = heptavint_decode(&vec->digits[i]);
    }
}

/* --- Test functions --- */

static void batch_6502(void)
{
    SECTION("Heptavint Encoding");
    TEST("Encode 0 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(0, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(hv.hi == 0 && hv.lo == 0, "0 = (0,0)");
    PASS();
}

static void batch_6503(void)
{
    TEST("Encode +1 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(1, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(heptavint_decode(&hv) == 1, "decode must give 1");
    PASS();
}

static void batch_6504(void)
{
    TEST("Encode -1 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(-1, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(heptavint_decode(&hv) == -1, "decode must give -1");
    PASS();
}

static void batch_6505(void)
{
    TEST("Encode +2 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(2, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(heptavint_decode(&hv) == 2, "decode must give 2");
    PASS();
}

static void batch_6506(void)
{
    TEST("Encode -2 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(-2, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(heptavint_decode(&hv) == -2, "decode must give -2");
    PASS();
}

static void batch_6507(void)
{
    TEST("Encode +3 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(3, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(heptavint_decode(&hv) == 3, "decode must give 3");
    PASS();
}

static void batch_6508(void)
{
    TEST("Encode -3 into heptavint");
    heptavint_t hv;
    int rc = heptavint_encode(-3, &hv);
    ASSERT(rc == 0, "encode should succeed");
    ASSERT(heptavint_decode(&hv) == -3, "decode must give -3");
    PASS();
}

static void batch_6509(void)
{
    TEST("Round-trip all 7 heptavint values");
    for (int v = -3; v <= 3; v++)
    {
        heptavint_t hv;
        int rc = heptavint_encode(v, &hv);
        ASSERT(rc == 0, "encode must succeed for valid value");
        ASSERT(heptavint_decode(&hv) == v, "round-trip must preserve value");
    }
    PASS();
}

static void batch_6510(void)
{
    TEST("Overflow detection: +4 rejected");
    heptavint_t hv;
    int rc = heptavint_encode(4, &hv);
    ASSERT(rc == -1, "+4 exceeds heptavint range");
    PASS();
}

static void batch_6511(void)
{
    TEST("Overflow detection: -4 rejected");
    heptavint_t hv;
    int rc = heptavint_encode(-4, &hv);
    ASSERT(rc == -1, "-4 exceeds heptavint range");
    PASS();
}

static void batch_6512(void)
{
    TEST("Overflow detection: +10 rejected");
    heptavint_t hv;
    int rc = heptavint_encode(10, &hv);
    ASSERT(rc == -1, "+10 exceeds heptavint range");
    PASS();
}

static void batch_6513(void)
{
    TEST("Zero representation check");
    heptavint_t hv;
    heptavint_encode(0, &hv);
    ASSERT(heptavint_is_zero(&hv), "0 should be zero");
    PASS();
}

static void batch_6514(void)
{
    TEST("Non-zero representation check +1");
    heptavint_t hv;
    heptavint_encode(1, &hv);
    ASSERT(!heptavint_is_zero(&hv), "+1 should not be zero");
    PASS();
}

static void batch_6515(void)
{
    TEST("Non-zero representation check -3");
    heptavint_t hv;
    heptavint_encode(-3, &hv);
    ASSERT(!heptavint_is_zero(&hv), "-3 should not be zero");
    PASS();
}

static void batch_6516(void)
{
    TEST("Heptavint add: 0 + 0 = 0");
    heptavint_t a, b, r;
    heptavint_encode(0, &a);
    heptavint_encode(0, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == 0, "0+0=0");
    PASS();
}

static void batch_6517(void)
{
    TEST("Heptavint add: 1 + 1 = 2");
    heptavint_t a, b, r;
    heptavint_encode(1, &a);
    heptavint_encode(1, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == 2, "1+1=2");
    PASS();
}

static void batch_6518(void)
{
    TEST("Heptavint add: 1 + (-1) = 0");
    heptavint_t a, b, r;
    heptavint_encode(1, &a);
    heptavint_encode(-1, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == 0, "1+(-1)=0");
    PASS();
}

static void batch_6519(void)
{
    TEST("Heptavint add: 3 + (-3) = 0");
    heptavint_t a, b, r;
    heptavint_encode(3, &a);
    heptavint_encode(-3, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == 0, "3+(-3)=0");
    PASS();
}

static void batch_6520(void)
{
    TEST("Heptavint add overflow: 2 + 2 = 4 (overflow)");
    heptavint_t a, b, r;
    heptavint_encode(2, &a);
    heptavint_encode(2, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == -1, "2+2=4 overflows heptavint");
    PASS();
}

static void batch_6521(void)
{
    TEST("Heptavint add overflow: -2 + (-2) = -4 (overflow)");
    heptavint_t a, b, r;
    heptavint_encode(-2, &a);
    heptavint_encode(-2, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == -1, "-2+(-2)=-4 overflows heptavint");
    PASS();
}

static void batch_6522(void)
{
    TEST("Heptavint add: -1 + (-2) = -3");
    heptavint_t a, b, r;
    heptavint_encode(-1, &a);
    heptavint_encode(-2, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == -3, "-1+(-2)=-3");
    PASS();
}

static void batch_6523(void)
{
    TEST("Heptavint negate: neg(+2) = -2");
    heptavint_t a, r;
    heptavint_encode(2, &a);
    heptavint_negate(&a, &r);
    ASSERT(heptavint_decode(&r) == -2, "neg(2)=-2");
    PASS();
}

static void batch_6524(void)
{
    TEST("Heptavint negate: neg(0) = 0");
    heptavint_t a, r;
    heptavint_encode(0, &a);
    heptavint_negate(&a, &r);
    ASSERT(heptavint_decode(&r) == 0, "neg(0)=0");
    PASS();
}

static void batch_6525(void)
{
    TEST("Heptavint negate: neg(-3) = +3");
    heptavint_t a, r;
    heptavint_encode(-3, &a);
    heptavint_negate(&a, &r);
    ASSERT(heptavint_decode(&r) == 3, "neg(-3)=+3");
    PASS();
}

static void batch_6526(void)
{
    TEST("Heptavint double-negate round-trip");
    for (int v = -3; v <= 3; v++)
    {
        heptavint_t a, n1, n2;
        heptavint_encode(v, &a);
        heptavint_negate(&a, &n1);
        heptavint_negate(&n1, &n2);
        ASSERT(heptavint_decode(&n2) == v, "double negate restores value");
    }
    PASS();
}

static void batch_6527(void)
{
    TEST("Heptavint validity: (1,1) = 4 invalid");
    heptavint_t hv = {.hi = TRIT_TRUE, .lo = TRIT_TRUE};
    ASSERT(!heptavint_valid(&hv), "hi=1,lo=1 -> 4 out of range");
    PASS();
}

static void batch_6528(void)
{
    TEST("Heptavint validity: (-1,-1) = -4 invalid");
    heptavint_t hv = {.hi = TRIT_FALSE, .lo = TRIT_FALSE};
    ASSERT(!heptavint_valid(&hv), "hi=-1,lo=-1 -> -4 out of range");
    PASS();
}

static void batch_6529(void)
{
    TEST("Heptavint validity: (1,0) = 3 valid");
    heptavint_t hv = {.hi = TRIT_TRUE, .lo = TRIT_UNKNOWN};
    ASSERT(heptavint_valid(&hv), "hi=1,lo=0 -> 3 is valid");
    PASS();
}

static void batch_6530(void)
{
    TEST("Base-3 encode/decode round-trip for -4..+4");
    for (int v = -4; v <= 4; v++)
    {
        trit hi, lo;
        base3_encode(v, &hi, &lo);
        int decoded = base3_decode(hi, lo);
        ASSERT(decoded == v, "base3 round-trip must work");
    }
    PASS();
}

static void batch_6531(void)
{
    TEST("Radix conversion: base-3 to heptavint for valid range");
    for (int v = -3; v <= 3; v++)
    {
        trit hi, lo;
        base3_encode(v, &hi, &lo);
        heptavint_t hv;
        heptavint_encode(v, &hv);
        /* Both should decode to same value */
        ASSERT(base3_decode(hi, lo) == heptavint_decode(&hv), "same value");
    }
    PASS();
}

static void batch_6532(void)
{
    TEST("Heptavint vector pack: {0, 1, -1}");
    int vals[] = {0, 1, -1};
    heptavint_vec_t vec;
    int rc = heptavint_vec_pack(vals, 3, &vec);
    ASSERT(rc == 0, "pack should succeed");
    ASSERT(vec.len == 3, "length=3");
    PASS();
}

static void batch_6533(void)
{
    TEST("Heptavint vector unpack round-trip");
    int vals[] = {-3, 0, 2, -1};
    heptavint_vec_t vec;
    heptavint_vec_pack(vals, 4, &vec);
    int out[4];
    heptavint_vec_unpack(&vec, out);
    for (int i = 0; i < 4; i++)
    {
        ASSERT(out[i] == vals[i], "unpack must match pack");
    }
    PASS();
}

static void batch_6534(void)
{
    TEST("Heptavint vector pack overflow: value 5 rejected");
    int vals[] = {0, 5};
    heptavint_vec_t vec;
    int rc = heptavint_vec_pack(vals, 2, &vec);
    ASSERT(rc == -1, "value 5 should cause pack failure");
    PASS();
}

static void batch_6535(void)
{
    TEST("Heptavint vector pack: too many digits rejected");
    int vals[] = {0, 1, 2, 3, -1};
    heptavint_vec_t vec;
    int rc = heptavint_vec_pack(vals, 5, &vec);
    ASSERT(rc == -1, "5 digits exceed capacity 4");
    PASS();
}

static void batch_6536(void)
{
    TEST("Heptavint add: 2 + 1 = 3");
    heptavint_t a, b, r;
    heptavint_encode(2, &a);
    heptavint_encode(1, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == 3, "2+1=3");
    PASS();
}

static void batch_6537(void)
{
    TEST("Heptavint add: -2 + (-1) = -3");
    heptavint_t a, b, r;
    heptavint_encode(-2, &a);
    heptavint_encode(-1, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == -3, "-2+(-1)=-3");
    PASS();
}

static void batch_6538(void)
{
    TEST("Heptavint add: 3 + 0 = 3");
    heptavint_t a, b, r;
    heptavint_encode(3, &a);
    heptavint_encode(0, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == 0, "add should succeed");
    ASSERT(heptavint_decode(&r) == 3, "3+0=3");
    PASS();
}

static void batch_6539(void)
{
    TEST("Heptavint add: 3 + 1 = 4 (overflow)");
    heptavint_t a, b, r;
    heptavint_encode(3, &a);
    heptavint_encode(1, &b);
    int rc = heptavint_add(&a, &b, &r);
    ASSERT(rc == -1, "3+1=4 overflows");
    PASS();
}

static void batch_6540(void)
{
    TEST("Heptavint encode trit representation for +3");
    heptavint_t hv;
    heptavint_encode(3, &hv);
    ASSERT(hv.hi == TRIT_TRUE && hv.lo == TRIT_UNKNOWN, "+3 = (1,0)");
    PASS();
}

static void batch_6541(void)
{
    TEST("Heptavint encode trit representation for -3");
    heptavint_t hv;
    heptavint_encode(-3, &hv);
    ASSERT(hv.hi == TRIT_FALSE && hv.lo == TRIT_UNKNOWN, "-3 = (-1,0)");
    PASS();
}

static void batch_6542(void)
{
    TEST("Heptavint encode trit representation for +1");
    heptavint_t hv;
    heptavint_encode(1, &hv);
    ASSERT(hv.hi == TRIT_UNKNOWN && hv.lo == TRIT_TRUE, "+1 = (0,1)");
    PASS();
}

static void batch_6543(void)
{
    TEST("Heptavint encode trit representation for -1");
    heptavint_t hv;
    heptavint_encode(-1, &hv);
    ASSERT(hv.hi == TRIT_UNKNOWN && hv.lo == TRIT_FALSE, "-1 = (0,-1)");
    PASS();
}

static void batch_6544(void)
{
    TEST("Heptavint encode trit representation for +2");
    heptavint_t hv;
    heptavint_encode(2, &hv);
    /* 2 = 1*3 + (-1), so hi=1, lo=-1 */
    ASSERT(hv.hi == TRIT_TRUE && hv.lo == TRIT_FALSE, "+2 = (1,-1)");
    PASS();
}

static void batch_6545(void)
{
    TEST("Heptavint encode trit representation for -2");
    heptavint_t hv;
    heptavint_encode(-2, &hv);
    /* -2 = (-1)*3 + 1, so hi=-1, lo=1 */
    ASSERT(hv.hi == TRIT_FALSE && hv.lo == TRIT_TRUE, "-2 = (-1,1)");
    PASS();
}

static void batch_6546(void)
{
    TEST("Heptavint vector: all zeros");
    int vals[] = {0, 0, 0, 0};
    heptavint_vec_t vec;
    heptavint_vec_pack(vals, 4, &vec);
    for (int i = 0; i < 4; i++)
    {
        ASSERT(heptavint_is_zero(&vec.digits[i]), "all digits zero");
    }
    PASS();
}

static void batch_6547(void)
{
    TEST("Heptavint vector: mixed values decode correctly");
    int vals[] = {3, -2, 1, 0};
    heptavint_vec_t vec;
    heptavint_vec_pack(vals, 4, &vec);
    int out[4];
    heptavint_vec_unpack(&vec, out);
    ASSERT(out[0] == 3, "digit 0");
    ASSERT(out[1] == -2, "digit 1");
    ASSERT(out[2] == 1, "digit 2");
    ASSERT(out[3] == 0, "digit 3");
    PASS();
}

static void batch_6548(void)
{
    TEST("Heptavint add commutative: a+b == b+a for all valid pairs");
    int ok = 1;
    for (int a = -3; a <= 3 && ok; a++)
    {
        for (int b = -3; b <= 3 && ok; b++)
        {
            heptavint_t ha, hb, r1, r2;
            heptavint_encode(a, &ha);
            heptavint_encode(b, &hb);
            int rc1 = heptavint_add(&ha, &hb, &r1);
            int rc2 = heptavint_add(&hb, &ha, &r2);
            if (rc1 != rc2)
                ok = 0;
            if (rc1 == 0 && heptavint_decode(&r1) != heptavint_decode(&r2))
                ok = 0;
        }
    }
    ASSERT(ok, "addition is commutative");
    PASS();
}

static void batch_6549(void)
{
    TEST("Heptavint identity: a + 0 = a for all a");
    for (int a = -3; a <= 3; a++)
    {
        heptavint_t ha, hz, r;
        heptavint_encode(a, &ha);
        heptavint_encode(0, &hz);
        int rc = heptavint_add(&ha, &hz, &r);
        ASSERT(rc == 0, "add zero must succeed");
        ASSERT(heptavint_decode(&r) == a, "a+0=a");
    }
    PASS();
}

static void batch_6550(void)
{
    TEST("Heptavint inverse: a + neg(a) = 0 for all a");
    for (int a = -3; a <= 3; a++)
    {
        heptavint_t ha, hn, r;
        heptavint_encode(a, &ha);
        heptavint_negate(&ha, &hn);
        int rc = heptavint_add(&ha, &hn, &r);
        ASSERT(rc == 0, "add inverse must succeed");
        ASSERT(heptavint_decode(&r) == 0, "a+(-a)=0");
    }
    PASS();
}

static void batch_6551(void)
{
    TEST("Heptavint: all 7 encoded values have valid trits");
    for (int v = -3; v <= 3; v++)
    {
        heptavint_t hv;
        heptavint_encode(v, &hv);
        ASSERT(hv.hi >= -1 && hv.hi <= 1, "hi trit in range");
        ASSERT(hv.lo >= -1 && hv.lo <= 1, "lo trit in range");
        ASSERT(heptavint_valid(&hv), "encoded value must be valid");
    }
    PASS();
}

int main(void)
{
    printf("=== Batch 115: Tests 6502-6551 — Heptavint Multi-Radix Encoding ===\n");
    batch_6502();
    batch_6503();
    batch_6504();
    batch_6505();
    batch_6506();
    batch_6507();
    batch_6508();
    batch_6509();
    batch_6510();
    batch_6511();
    batch_6512();
    batch_6513();
    batch_6514();
    batch_6515();
    batch_6516();
    batch_6517();
    batch_6518();
    batch_6519();
    batch_6520();
    batch_6521();
    batch_6522();
    batch_6523();
    batch_6524();
    batch_6525();
    batch_6526();
    batch_6527();
    batch_6528();
    batch_6529();
    batch_6530();
    batch_6531();
    batch_6532();
    batch_6533();
    batch_6534();
    batch_6535();
    batch_6536();
    batch_6537();
    batch_6538();
    batch_6539();
    batch_6540();
    batch_6541();
    batch_6542();
    batch_6543();
    batch_6544();
    batch_6545();
    batch_6546();
    batch_6547();
    batch_6548();
    batch_6549();
    batch_6550();
    batch_6551();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return fail_count ? 1 : 0;
}
