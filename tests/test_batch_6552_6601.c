/*==============================================================================
 * Batch 116 – Tests 6552-6601: Ternary Floating-Point Basics
 * Tests a simple balanced ternary float format: sign + 4-trit mantissa +
 * 2-trit exponent = 7 trits total.
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

/* ---- Ternary Floating-Point Format ---- */
/* tfloat_t: 7-trit floating-point number                                    */
/*   sign:       +1 = positive, -1 = negative, 0 = zero/special             */
/*   mantissa:   4 trits, balanced ternary, represents |value| portion       */
/*               mantissa value = m[0]*27 + m[1]*9 + m[2]*3 + m[3]          */
/*               range: -40..+40                                              */
/*   exponent:   2 trits, represents power of 3                              */
/*               exponent value = e[0]*3 + e[1], range: -4..+4               */
/*   Decoded value = sign * mantissa_value * 3^exponent_value                */

typedef struct
{
    trit sign;
    trit mantissa[4];
    trit exponent[2];
} tfloat_t;

/* Decode balanced ternary from trit array */
static int bt_decode4(const trit *t)
{
    return t[0] * 27 + t[1] * 9 + t[2] * 3 + t[3];
}

static int bt_decode2(const trit *t)
{
    return t[0] * 3 + t[1];
}

/* Encode integer into 4-trit balanced ternary */
static void bt_encode4(int val, trit *t)
{
    for (int i = 3; i >= 0; i--)
    {
        int r = val % 3;
        val = val / 3;
        if (r > 1)
        {
            r -= 3;
            val += 1;
        }
        if (r < -1)
        {
            r += 3;
            val -= 1;
        }
        t[i] = (trit)r;
    }
}

/* Encode integer into 2-trit balanced ternary */
static void bt_encode2(int val, trit *t)
{
    for (int i = 1; i >= 0; i--)
    {
        int r = val % 3;
        val = val / 3;
        if (r > 1)
        {
            r -= 3;
            val += 1;
        }
        if (r < -1)
        {
            r += 3;
            val -= 1;
        }
        t[i] = (trit)r;
    }
}

/* Integer power of 3 */
static int pow3(int exp)
{
    int result = 1;
    int e = exp < 0 ? -exp : exp;
    for (int i = 0; i < e; i++)
        result *= 3;
    /* For negative exponents, we'd need fractions. We'll only use non-negative
       exponents for integer encoding. */
    return result;
}

/* Encode a small integer into tfloat */
static void tfloat_from_int(int value, tfloat_t *f)
{
    memset(f, 0, sizeof(*f));
    if (value == 0)
    {
        f->sign = TRIT_UNKNOWN;
        return;
    }
    f->sign = (value > 0) ? TRIT_TRUE : TRIT_FALSE;
    int absval = (value < 0) ? -value : value;

    /* Find smallest exponent such that absval / 3^exp fits in 4-trit mantissa (max 40) */
    int exp = 0;
    int mval = absval;
    while (mval > 40 && exp < 4)
    {
        /* mval must be divisible by 3 for exact representation */
        if (mval % 3 != 0)
            break;
        mval /= 3;
        exp++;
    }
    bt_encode4(mval, f->mantissa);
    bt_encode2(exp, f->exponent);
}

/* Decode tfloat to integer (only exact for representable integers) */
static int tfloat_to_int(const tfloat_t *f)
{
    if (f->sign == TRIT_UNKNOWN)
        return 0;
    int mval = bt_decode4(f->mantissa);
    int exp = bt_decode2(f->exponent);
    int result = mval;
    if (exp >= 0)
    {
        result *= pow3(exp);
    }
    return (f->sign == TRIT_FALSE) ? -result : result;
}

/* Check if tfloat is zero */
static int tfloat_is_zero(const tfloat_t *f)
{
    return (f->sign == TRIT_UNKNOWN);
}

/* Negate a tfloat */
static void tfloat_negate(const tfloat_t *in, tfloat_t *out)
{
    *out = *in;
    out->sign = trit_not(in->sign);
}

/* Compare two tfloat values (by converting to int, for simplicity) */
static int tfloat_compare(const tfloat_t *a, const tfloat_t *b)
{
    int va = tfloat_to_int(a);
    int vb = tfloat_to_int(b);
    if (va < vb)
        return -1;
    if (va > vb)
        return +1;
    return 0;
}

/* Add two tfloat values (simple: convert to int, add, convert back) */
static void tfloat_add(const tfloat_t *a, const tfloat_t *b, tfloat_t *result)
{
    int va = tfloat_to_int(a);
    int vb = tfloat_to_int(b);
    tfloat_from_int(va + vb, result);
}

/* Check if mantissa is normalized: leading trit should be non-zero if value != 0 */
static int tfloat_mantissa_normalized(const tfloat_t *f)
{
    if (tfloat_is_zero(f))
        return 1; /* zero is trivially normalized */
    return (f->mantissa[0] != TRIT_UNKNOWN);
}

/* Check if exponent overflows (outside -4..+4) */
static int tfloat_exponent_valid(const tfloat_t *f)
{
    int exp = bt_decode2(f->exponent);
    return (exp >= -4 && exp <= 4);
}

/* --- Test functions --- */

static void batch_6552(void)
{
    SECTION("Ternary Floating-Point Basics");
    TEST("Encode 0.0");
    tfloat_t f;
    tfloat_from_int(0, &f);
    ASSERT(tfloat_is_zero(&f), "0 should be zero");
    ASSERT(tfloat_to_int(&f) == 0, "decoded value = 0");
    PASS();
}

static void batch_6553(void)
{
    TEST("Encode +1.0");
    tfloat_t f;
    tfloat_from_int(1, &f);
    ASSERT(f.sign == TRIT_TRUE, "sign = positive");
    ASSERT(tfloat_to_int(&f) == 1, "decoded = 1");
    PASS();
}

static void batch_6554(void)
{
    TEST("Encode -1.0");
    tfloat_t f;
    tfloat_from_int(-1, &f);
    ASSERT(f.sign == TRIT_FALSE, "sign = negative");
    ASSERT(tfloat_to_int(&f) == -1, "decoded = -1");
    PASS();
}

static void batch_6555(void)
{
    TEST("Encode +3");
    tfloat_t f;
    tfloat_from_int(3, &f);
    ASSERT(tfloat_to_int(&f) == 3, "decoded = 3");
    PASS();
}

static void batch_6556(void)
{
    TEST("Encode -3");
    tfloat_t f;
    tfloat_from_int(-3, &f);
    ASSERT(tfloat_to_int(&f) == -3, "decoded = -3");
    PASS();
}

static void batch_6557(void)
{
    TEST("Encode +9");
    tfloat_t f;
    tfloat_from_int(9, &f);
    ASSERT(tfloat_to_int(&f) == 9, "decoded = 9");
    PASS();
}

static void batch_6558(void)
{
    TEST("Encode -9");
    tfloat_t f;
    tfloat_from_int(-9, &f);
    ASSERT(tfloat_to_int(&f) == -9, "decoded = -9");
    PASS();
}

static void batch_6559(void)
{
    TEST("Encode +13 (max 4-trit balanced ternary = 1*27+1*9+1*3+1 = 40, 13 fits)");
    tfloat_t f;
    tfloat_from_int(13, &f);
    ASSERT(tfloat_to_int(&f) == 13, "decoded = 13");
    PASS();
}

static void batch_6560(void)
{
    TEST("Encode -13");
    tfloat_t f;
    tfloat_from_int(-13, &f);
    ASSERT(tfloat_to_int(&f) == -13, "decoded = -13");
    PASS();
}

static void batch_6561(void)
{
    TEST("Round-trip encode/decode for 0");
    tfloat_t f;
    tfloat_from_int(0, &f);
    ASSERT(tfloat_to_int(&f) == 0, "round-trip 0");
    PASS();
}

static void batch_6562(void)
{
    TEST("Round-trip for positive values 1..13");
    for (int v = 1; v <= 13; v++)
    {
        tfloat_t f;
        tfloat_from_int(v, &f);
        ASSERT(tfloat_to_int(&f) == v, "round-trip positive");
    }
    PASS();
}

static void batch_6563(void)
{
    TEST("Round-trip for negative values -1..-13");
    for (int v = -13; v <= -1; v++)
    {
        tfloat_t f;
        tfloat_from_int(v, &f);
        ASSERT(tfloat_to_int(&f) == v, "round-trip negative");
    }
    PASS();
}

static void batch_6564(void)
{
    TEST("tfloat_negate: neg(+5) = -5");
    tfloat_t a, r;
    tfloat_from_int(5, &a);
    tfloat_negate(&a, &r);
    ASSERT(tfloat_to_int(&r) == -5, "neg(5) = -5");
    PASS();
}

static void batch_6565(void)
{
    TEST("tfloat_negate: neg(0) sign is unknown");
    tfloat_t a, r;
    tfloat_from_int(0, &a);
    tfloat_negate(&a, &r);
    ASSERT(tfloat_is_zero(&r), "neg(0) is zero");
    PASS();
}

static void batch_6566(void)
{
    TEST("tfloat_negate: neg(-7) = +7");
    tfloat_t a, r;
    tfloat_from_int(-7, &a);
    tfloat_negate(&a, &r);
    ASSERT(tfloat_to_int(&r) == 7, "neg(-7) = 7");
    PASS();
}

static void batch_6567(void)
{
    TEST("tfloat_negate: double negate round-trip");
    for (int v = -13; v <= 13; v++)
    {
        tfloat_t a, n1, n2;
        tfloat_from_int(v, &a);
        tfloat_negate(&a, &n1);
        tfloat_negate(&n1, &n2);
        ASSERT(tfloat_to_int(&n2) == v, "double negate restores");
    }
    PASS();
}

static void batch_6568(void)
{
    TEST("tfloat_is_zero: 0 is zero");
    tfloat_t f;
    tfloat_from_int(0, &f);
    ASSERT(tfloat_is_zero(&f), "0 is zero");
    PASS();
}

static void batch_6569(void)
{
    TEST("tfloat_is_zero: 1 is not zero");
    tfloat_t f;
    tfloat_from_int(1, &f);
    ASSERT(!tfloat_is_zero(&f), "1 is not zero");
    PASS();
}

static void batch_6570(void)
{
    TEST("tfloat_is_zero: -1 is not zero");
    tfloat_t f;
    tfloat_from_int(-1, &f);
    ASSERT(!tfloat_is_zero(&f), "-1 is not zero");
    PASS();
}

static void batch_6571(void)
{
    TEST("tfloat_compare: 0 == 0");
    tfloat_t a, b;
    tfloat_from_int(0, &a);
    tfloat_from_int(0, &b);
    ASSERT(tfloat_compare(&a, &b) == 0, "0 == 0");
    PASS();
}

static void batch_6572(void)
{
    TEST("tfloat_compare: 1 > 0");
    tfloat_t a, b;
    tfloat_from_int(1, &a);
    tfloat_from_int(0, &b);
    ASSERT(tfloat_compare(&a, &b) > 0, "1 > 0");
    PASS();
}

static void batch_6573(void)
{
    TEST("tfloat_compare: -1 < 0");
    tfloat_t a, b;
    tfloat_from_int(-1, &a);
    tfloat_from_int(0, &b);
    ASSERT(tfloat_compare(&a, &b) < 0, "-1 < 0");
    PASS();
}

static void batch_6574(void)
{
    TEST("tfloat_compare: 5 > 3");
    tfloat_t a, b;
    tfloat_from_int(5, &a);
    tfloat_from_int(3, &b);
    ASSERT(tfloat_compare(&a, &b) > 0, "5 > 3");
    PASS();
}

static void batch_6575(void)
{
    TEST("tfloat_compare: -5 < -3");
    tfloat_t a, b;
    tfloat_from_int(-5, &a);
    tfloat_from_int(-3, &b);
    ASSERT(tfloat_compare(&a, &b) < 0, "-5 < -3");
    PASS();
}

static void batch_6576(void)
{
    TEST("tfloat_compare: 13 == 13");
    tfloat_t a, b;
    tfloat_from_int(13, &a);
    tfloat_from_int(13, &b);
    ASSERT(tfloat_compare(&a, &b) == 0, "13 == 13");
    PASS();
}

static void batch_6577(void)
{
    TEST("tfloat_add: 0 + 0 = 0");
    tfloat_t a, b, r;
    tfloat_from_int(0, &a);
    tfloat_from_int(0, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == 0, "0+0=0");
    PASS();
}

static void batch_6578(void)
{
    TEST("tfloat_add: 1 + 1 = 2");
    tfloat_t a, b, r;
    tfloat_from_int(1, &a);
    tfloat_from_int(1, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == 2, "1+1=2");
    PASS();
}

static void batch_6579(void)
{
    TEST("tfloat_add: 5 + (-5) = 0");
    tfloat_t a, b, r;
    tfloat_from_int(5, &a);
    tfloat_from_int(-5, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == 0, "5+(-5)=0");
    PASS();
}

static void batch_6580(void)
{
    TEST("tfloat_add: 3 + 4 = 7");
    tfloat_t a, b, r;
    tfloat_from_int(3, &a);
    tfloat_from_int(4, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == 7, "3+4=7");
    PASS();
}

static void batch_6581(void)
{
    TEST("tfloat_add: -3 + (-4) = -7");
    tfloat_t a, b, r;
    tfloat_from_int(-3, &a);
    tfloat_from_int(-4, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == -7, "-3+(-4)=-7");
    PASS();
}

static void batch_6582(void)
{
    TEST("tfloat_add: 10 + 3 = 13");
    tfloat_t a, b, r;
    tfloat_from_int(10, &a);
    tfloat_from_int(3, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == 13, "10+3=13");
    PASS();
}

static void batch_6583(void)
{
    TEST("tfloat: sign trit of positive is +1");
    tfloat_t f;
    tfloat_from_int(7, &f);
    ASSERT(f.sign == TRIT_TRUE, "positive sign");
    PASS();
}

static void batch_6584(void)
{
    TEST("tfloat: sign trit of negative is -1");
    tfloat_t f;
    tfloat_from_int(-7, &f);
    ASSERT(f.sign == TRIT_FALSE, "negative sign");
    PASS();
}

static void batch_6585(void)
{
    TEST("tfloat: sign trit of zero is 0");
    tfloat_t f;
    tfloat_from_int(0, &f);
    ASSERT(f.sign == TRIT_UNKNOWN, "zero sign");
    PASS();
}

static void batch_6586(void)
{
    TEST("tfloat mantissa: value 1 mantissa decodes to 1");
    tfloat_t f;
    tfloat_from_int(1, &f);
    int mval = bt_decode4(f.mantissa);
    ASSERT(mval == 1, "mantissa of 1 = 1");
    PASS();
}

static void batch_6587(void)
{
    TEST("tfloat mantissa: value 13 mantissa decodes to 13");
    tfloat_t f;
    tfloat_from_int(13, &f);
    int mval = bt_decode4(f.mantissa);
    int exp = bt_decode2(f.exponent);
    ASSERT(mval * pow3(exp) == 13, "mantissa*3^exp = 13");
    PASS();
}

static void batch_6588(void)
{
    TEST("tfloat exponent: value 1 has exponent 0");
    tfloat_t f;
    tfloat_from_int(1, &f);
    int exp = bt_decode2(f.exponent);
    ASSERT(exp == 0, "exp = 0 for value 1");
    PASS();
}

static void batch_6589(void)
{
    TEST("tfloat exponent: all small values have valid exponent");
    for (int v = -13; v <= 13; v++)
    {
        tfloat_t f;
        tfloat_from_int(v, &f);
        ASSERT(tfloat_exponent_valid(&f), "exponent in valid range");
    }
    PASS();
}

static void batch_6590(void)
{
    TEST("tfloat: mantissa trits are valid (-1, 0, +1)");
    for (int v = -13; v <= 13; v++)
    {
        tfloat_t f;
        tfloat_from_int(v, &f);
        for (int i = 0; i < 4; i++)
        {
            ASSERT(f.mantissa[i] >= -1 && f.mantissa[i] <= 1, "mantissa trit valid");
        }
    }
    PASS();
}

static void batch_6591(void)
{
    TEST("tfloat: exponent trits are valid (-1, 0, +1)");
    for (int v = -13; v <= 13; v++)
    {
        tfloat_t f;
        tfloat_from_int(v, &f);
        for (int i = 0; i < 2; i++)
        {
            ASSERT(f.exponent[i] >= -1 && f.exponent[i] <= 1, "exponent trit valid");
        }
    }
    PASS();
}

static void batch_6592(void)
{
    TEST("tfloat: sign trit is valid");
    for (int v = -13; v <= 13; v++)
    {
        tfloat_t f;
        tfloat_from_int(v, &f);
        ASSERT(f.sign >= -1 && f.sign <= 1, "sign trit valid");
    }
    PASS();
}

static void batch_6593(void)
{
    TEST("tfloat_add: commutative for small values");
    int ok = 1;
    for (int a = -5; a <= 5 && ok; a++)
    {
        for (int b = -5; b <= 5 && ok; b++)
        {
            tfloat_t fa, fb, r1, r2;
            tfloat_from_int(a, &fa);
            tfloat_from_int(b, &fb);
            tfloat_add(&fa, &fb, &r1);
            tfloat_add(&fb, &fa, &r2);
            if (tfloat_to_int(&r1) != tfloat_to_int(&r2))
                ok = 0;
        }
    }
    ASSERT(ok, "addition commutative");
    PASS();
}

static void batch_6594(void)
{
    TEST("tfloat_add: identity a + 0 = a");
    for (int a = -13; a <= 13; a++)
    {
        tfloat_t fa, fz, r;
        tfloat_from_int(a, &fa);
        tfloat_from_int(0, &fz);
        tfloat_add(&fa, &fz, &r);
        ASSERT(tfloat_to_int(&r) == a, "a+0=a");
    }
    PASS();
}

static void batch_6595(void)
{
    TEST("tfloat_compare: total order on -5..5");
    for (int a = -5; a <= 5; a++)
    {
        for (int b = -5; b <= 5; b++)
        {
            tfloat_t fa, fb;
            tfloat_from_int(a, &fa);
            tfloat_from_int(b, &fb);
            int cmp = tfloat_compare(&fa, &fb);
            if (a < b)
            {
                ASSERT(cmp < 0, "a<b => cmp<0");
            }
            else if (a > b)
            {
                ASSERT(cmp > 0, "a>b => cmp>0");
            }
            else
            {
                ASSERT(cmp == 0, "a==b => cmp==0");
            }
        }
    }
    PASS();
}

static void batch_6596(void)
{
    TEST("tfloat: struct size is 7 bytes and mantissa normalization");
    ASSERT(sizeof(tfloat_t) == 7, "tfloat is 7 trits = 7 bytes");
    /* 40 = 1*27 + 1*9 + 1*3 + 1 -> leading trit is 1 -> normalized */
    tfloat_t f;
    tfloat_from_int(40, &f);
    ASSERT(tfloat_mantissa_normalized(&f), "40 has normalized mantissa");
    tfloat_from_int(0, &f);
    ASSERT(tfloat_mantissa_normalized(&f), "0 trivially normalized");
    PASS();
}

static void batch_6597(void)
{
    TEST("tfloat_add: 1 + 2 = 3");
    tfloat_t a, b, r;
    tfloat_from_int(1, &a);
    tfloat_from_int(2, &b);
    tfloat_add(&a, &b, &r);
    ASSERT(tfloat_to_int(&r) == 3, "1+2=3");
    PASS();
}

static void batch_6598(void)
{
    TEST("tfloat_add: inverse a + (-a) = 0");
    for (int a = -13; a <= 13; a++)
    {
        tfloat_t fa, fn, r;
        tfloat_from_int(a, &fa);
        tfloat_negate(&fa, &fn);
        tfloat_add(&fa, &fn, &r);
        ASSERT(tfloat_to_int(&r) == 0, "a+(-a)=0");
    }
    PASS();
}

static void batch_6599(void)
{
    TEST("tfloat: encode +27 round-trip and structure");
    tfloat_t f;
    tfloat_from_int(27, &f);
    ASSERT(tfloat_to_int(&f) == 27, "decoded = 27");
    int mval = bt_decode4(f.mantissa);
    int exp = bt_decode2(f.exponent);
    ASSERT(mval * pow3(exp) == 27, "mantissa*3^exp = 27");
    ASSERT(f.sign == TRIT_TRUE, "positive sign");
    PASS();
}

static void batch_6600(void)
{
    TEST("tfloat: encode +40 (max mantissa)");
    tfloat_t f;
    tfloat_from_int(40, &f);
    ASSERT(tfloat_to_int(&f) == 40, "decoded = 40");
    PASS();
}

static void batch_6601(void)
{
    TEST("tfloat: encode -40 (min mantissa)");
    tfloat_t f;
    tfloat_from_int(-40, &f);
    ASSERT(tfloat_to_int(&f) == -40, "decoded = -40");
    PASS();
}

int main(void)
{
    printf("=== Batch 116: Tests 6552-6601 — Ternary Floating-Point Basics ===\n");
    batch_6552();
    batch_6553();
    batch_6554();
    batch_6555();
    batch_6556();
    batch_6557();
    batch_6558();
    batch_6559();
    batch_6560();
    batch_6561();
    batch_6562();
    batch_6563();
    batch_6564();
    batch_6565();
    batch_6566();
    batch_6567();
    batch_6568();
    batch_6569();
    batch_6570();
    batch_6571();
    batch_6572();
    batch_6573();
    batch_6574();
    batch_6575();
    batch_6576();
    batch_6577();
    batch_6578();
    batch_6579();
    batch_6580();
    batch_6581();
    batch_6582();
    batch_6583();
    batch_6584();
    batch_6585();
    batch_6586();
    batch_6587();
    batch_6588();
    batch_6589();
    batch_6590();
    batch_6591();
    batch_6592();
    batch_6593();
    batch_6594();
    batch_6595();
    batch_6596();
    batch_6597();
    batch_6598();
    batch_6599();
    batch_6600();
    batch_6601();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return fail_count ? 1 : 0;
}
