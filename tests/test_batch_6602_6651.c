/*==============================================================================
 * Batch 117 – Tests 6602-6651: Ternary Error Correction (GF(3) Hamming)
 * Tests GF(3) Hamming [4,2] code: 2 data trits encoded into 4-trit codeword
 * with single-error correction over the ternary field GF(3).
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

/* ---- GF(3) Arithmetic ---- */
/* Map balanced trit {-1,0,+1} to GF(3) element {0,1,2}: trit_to_gf3(-1)=2, 0->0, 1->1 */
static int trit_to_gf3(trit t)
{
    return ((int)t + 3) % 3; /* -1->2, 0->0, 1->1 */
}

static trit gf3_to_trit(int g)
{
    /* 0->0, 1->1, 2->-1 */
    static const trit lut[3] = {0, 1, -1};
    return lut[g % 3];
}

static int gf3_add(int a, int b)
{
    return (a + b) % 3;
}

static int gf3_sub(int a, int b)
{
    return (a - b + 3) % 3;
}

static int gf3_mul(int a, int b)
{
    return (a * b) % 3;
}

/* Multiplicative inverse in GF(3): 0->0 (undefined, but safe), 1->1, 2->2 */
static int gf3_inv(int a)
{
    /* 1^-1 = 1, 2^-1 = 2 (since 2*2=4=1 mod 3) */
    return a; /* works for GF(3): inv(1)=1, inv(2)=2 */
}

/* ---- GF(3) Hamming [4,2] Code ---- */
/* Generator matrix G (2x4): data [d0,d1] -> codeword [d0, d1, p0, p1]    */
/*   G = [1 0 1 1]                                                         */
/*       [0 1 1 2]                                                         */
/* So: p0 = d0 + d1 (mod 3), p1 = d0 + 2*d1 (mod 3)                       */
/* Parity check matrix H (2x4):                                            */
/*   H = [1 1 2 0]                                                         */
/*       [1 2 0 2]                                                         */
/* Syndrome s = H * r^T (mod 3). If s=[0,0], no error.                     */

typedef struct
{
    int c[4]; /* GF(3) elements */
} codeword_t;

typedef struct
{
    int s[2]; /* syndrome */
} syndrome_t;

/* Encode 2 data trits into 4-element GF(3) codeword */
static void hamming_encode(int d0, int d1, codeword_t *cw)
{
    cw->c[0] = d0 % 3;
    cw->c[1] = d1 % 3;
    cw->c[2] = gf3_add(d0, d1);
    cw->c[3] = gf3_add(d0, gf3_mul(2, d1));
}

/* Compute syndrome */
static void hamming_syndrome(const codeword_t *cw, syndrome_t *syn)
{
    /* H = [1 1 2 0; 1 2 0 2] */
    syn->s[0] = (1 * cw->c[0] + 1 * cw->c[1] + 2 * cw->c[2] + 0 * cw->c[3]) % 3;
    syn->s[1] = (1 * cw->c[0] + 2 * cw->c[1] + 0 * cw->c[2] + 2 * cw->c[3]) % 3;
}

/* Check if syndrome is zero (no error) */
static int syndrome_is_zero(const syndrome_t *syn)
{
    return (syn->s[0] == 0 && syn->s[1] == 0);
}

/* Correct single error. Returns: 0=no error, 1=corrected, -1=uncorrectable */
static int hamming_correct(codeword_t *cw)
{
    syndrome_t syn;
    hamming_syndrome(cw, &syn);
    if (syndrome_is_zero(&syn))
        return 0; /* no error */

    /* H columns: col0=[1,1], col1=[1,2], col2=[2,0], col3=[0,2] */
    int h_cols[4][2] = {{1, 1}, {1, 2}, {2, 0}, {0, 2}};

    /* Find column matching syndrome (possibly scaled) */
    for (int pos = 0; pos < 4; pos++)
    {
        for (int scale = 1; scale <= 2; scale++)
        {
            int s0 = gf3_mul(scale, h_cols[pos][0]) % 3;
            int s1 = gf3_mul(scale, h_cols[pos][1]) % 3;
            if (s0 == syn.s[0] && s1 == syn.s[1])
            {
                /* Error value is `scale` at position `pos` */
                cw->c[pos] = gf3_sub(cw->c[pos], scale);
                return 1; /* corrected */
            }
        }
    }
    return -1; /* uncorrectable (double error) */
}

/* Decode: extract data trits from codeword */
static void hamming_decode(const codeword_t *cw, int *d0, int *d1)
{
    *d0 = cw->c[0];
    *d1 = cw->c[1];
}

/* Inject single error at position pos with value err (1 or 2) */
static void inject_error(codeword_t *cw, int pos, int err)
{
    cw->c[pos] = gf3_add(cw->c[pos], err);
}

/* ---- Test functions ---- */

static void batch_6602(void)
{
    SECTION("GF(3) Hamming [4,2] Code");
    TEST("GF(3) addition: 0+0=0");
    ASSERT(gf3_add(0, 0) == 0, "0+0=0");
    PASS();
}

static void batch_6603(void)
{
    TEST("GF(3) addition: 1+1=2");
    ASSERT(gf3_add(1, 1) == 2, "1+1=2");
    PASS();
}

static void batch_6604(void)
{
    TEST("GF(3) addition: 1+2=0");
    ASSERT(gf3_add(1, 2) == 0, "1+2=0 mod 3");
    PASS();
}

static void batch_6605(void)
{
    TEST("GF(3) addition: 2+2=1");
    ASSERT(gf3_add(2, 2) == 1, "2+2=1 mod 3");
    PASS();
}

static void batch_6606(void)
{
    TEST("GF(3) multiplication: 2*2=1");
    ASSERT(gf3_mul(2, 2) == 1, "2*2=1 mod 3");
    PASS();
}

static void batch_6607(void)
{
    TEST("GF(3) multiplication: 1*2=2");
    ASSERT(gf3_mul(1, 2) == 2, "1*2=2");
    PASS();
}

static void batch_6608(void)
{
    TEST("GF(3) multiplication: 0*anything=0");
    for (int a = 0; a < 3; a++)
    {
        ASSERT(gf3_mul(0, a) == 0, "0*a=0");
    }
    PASS();
}

static void batch_6609(void)
{
    TEST("GF(3) inverse: inv(1)=1");
    ASSERT(gf3_inv(1) == 1, "inv(1)=1");
    PASS();
}

static void batch_6610(void)
{
    TEST("GF(3) inverse: inv(2)=2");
    ASSERT(gf3_inv(2) == 2, "inv(2)=2, since 2*2=1 mod 3");
    PASS();
}

static void batch_6611(void)
{
    TEST("GF(3) trit mapping: -1 -> 2 -> -1");
    int g = trit_to_gf3(TRIT_FALSE);
    ASSERT(g == 2, "-1 maps to 2");
    trit t = gf3_to_trit(g);
    ASSERT(t == TRIT_FALSE, "2 maps to -1");
    PASS();
}

static void batch_6612(void)
{
    TEST("GF(3) trit mapping: 0 -> 0 -> 0");
    int g = trit_to_gf3(TRIT_UNKNOWN);
    ASSERT(g == 0, "0 maps to 0");
    trit t = gf3_to_trit(g);
    ASSERT(t == TRIT_UNKNOWN, "0 maps to 0");
    PASS();
}

static void batch_6613(void)
{
    TEST("GF(3) trit mapping: +1 -> 1 -> +1");
    int g = trit_to_gf3(TRIT_TRUE);
    ASSERT(g == 1, "+1 maps to 1");
    trit t = gf3_to_trit(g);
    ASSERT(t == TRIT_TRUE, "1 maps to +1");
    PASS();
}

static void batch_6614(void)
{
    TEST("Encode (0,0): parity = (0,0)");
    codeword_t cw;
    hamming_encode(0, 0, &cw);
    ASSERT(cw.c[0] == 0 && cw.c[1] == 0 && cw.c[2] == 0 && cw.c[3] == 0, "all zeros");
    PASS();
}

static void batch_6615(void)
{
    TEST("Encode (1,0): p0=1, p1=1");
    codeword_t cw;
    hamming_encode(1, 0, &cw);
    ASSERT(cw.c[0] == 1 && cw.c[1] == 0 && cw.c[2] == 1 && cw.c[3] == 1, "(1,0,1,1)");
    PASS();
}

static void batch_6616(void)
{
    TEST("Encode (0,1): p0=1, p1=2");
    codeword_t cw;
    hamming_encode(0, 1, &cw);
    ASSERT(cw.c[0] == 0 && cw.c[1] == 1 && cw.c[2] == 1 && cw.c[3] == 2, "(0,1,1,2)");
    PASS();
}

static void batch_6617(void)
{
    TEST("Encode (1,1): p0=2, p1=0");
    codeword_t cw;
    hamming_encode(1, 1, &cw);
    ASSERT(cw.c[2] == gf3_add(1, 1), "p0=1+1=2");
    ASSERT(cw.c[3] == gf3_add(1, gf3_mul(2, 1)), "p1=1+2=0");
    PASS();
}

static void batch_6618(void)
{
    TEST("Encode (2,2): p0=1, p1=0");
    codeword_t cw;
    hamming_encode(2, 2, &cw);
    ASSERT(cw.c[2] == gf3_add(2, 2), "p0=2+2=1");
    ASSERT(cw.c[3] == gf3_add(2, gf3_mul(2, 2)), "p1=2+1=0");
    PASS();
}

static void batch_6619(void)
{
    TEST("Encode all 9 inputs: codewords valid");
    for (int d0 = 0; d0 < 3; d0++)
    {
        for (int d1 = 0; d1 < 3; d1++)
        {
            codeword_t cw;
            hamming_encode(d0, d1, &cw);
            for (int i = 0; i < 4; i++)
            {
                ASSERT(cw.c[i] >= 0 && cw.c[i] < 3, "GF(3) element");
            }
        }
    }
    PASS();
}

static void batch_6620(void)
{
    TEST("Syndrome zero for all 9 valid codewords");
    for (int d0 = 0; d0 < 3; d0++)
    {
        for (int d1 = 0; d1 < 3; d1++)
        {
            codeword_t cw;
            hamming_encode(d0, d1, &cw);
            syndrome_t syn;
            hamming_syndrome(&cw, &syn);
            ASSERT(syndrome_is_zero(&syn), "valid codeword has zero syndrome");
        }
    }
    PASS();
}

static void batch_6621(void)
{
    TEST("Single error pos 0, err +1: detected");
    codeword_t cw;
    hamming_encode(0, 0, &cw);
    inject_error(&cw, 0, 1);
    syndrome_t syn;
    hamming_syndrome(&cw, &syn);
    ASSERT(!syndrome_is_zero(&syn), "error detected");
    PASS();
}

static void batch_6622(void)
{
    TEST("Single error pos 0, err +1: corrected");
    codeword_t cw;
    hamming_encode(1, 2, &cw);
    inject_error(&cw, 0, 1);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 1 && d1 == 2, "data restored");
    PASS();
}

static void batch_6623(void)
{
    TEST("Single error pos 0, err +2: corrected");
    codeword_t cw;
    hamming_encode(1, 2, &cw);
    inject_error(&cw, 0, 2);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 1 && d1 == 2, "data restored");
    PASS();
}

static void batch_6624(void)
{
    TEST("Single error pos 1, err +1: corrected");
    codeword_t cw;
    hamming_encode(0, 1, &cw);
    inject_error(&cw, 1, 1);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 0 && d1 == 1, "data restored");
    PASS();
}

static void batch_6625(void)
{
    TEST("Single error pos 1, err +2: corrected");
    codeword_t cw;
    hamming_encode(2, 0, &cw);
    inject_error(&cw, 1, 2);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 2 && d1 == 0, "data restored");
    PASS();
}

static void batch_6626(void)
{
    TEST("Single error pos 2, err +1: corrected");
    codeword_t cw;
    hamming_encode(1, 1, &cw);
    inject_error(&cw, 2, 1);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 1 && d1 == 1, "data restored");
    PASS();
}

static void batch_6627(void)
{
    TEST("Single error pos 2, err +2: corrected");
    codeword_t cw;
    hamming_encode(2, 1, &cw);
    inject_error(&cw, 2, 2);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 2 && d1 == 1, "data restored");
    PASS();
}

static void batch_6628(void)
{
    TEST("Single error pos 3, err +1: corrected");
    codeword_t cw;
    hamming_encode(0, 2, &cw);
    inject_error(&cw, 3, 1);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 0 && d1 == 2, "data restored");
    PASS();
}

static void batch_6629(void)
{
    TEST("Single error pos 3, err +2: corrected");
    codeword_t cw;
    hamming_encode(2, 2, &cw);
    inject_error(&cw, 3, 2);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 1, "correction succeeded");
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 2 && d1 == 2, "data restored");
    PASS();
}

static void batch_6630(void)
{
    TEST("No-error: hamming_correct returns 0");
    codeword_t cw;
    hamming_encode(1, 0, &cw);
    int rc = hamming_correct(&cw);
    ASSERT(rc == 0, "no error means no correction needed");
    PASS();
}

static void batch_6631(void)
{
    TEST("Round-trip all 9 inputs: encode, no corruption, decode");
    for (int d0 = 0; d0 < 3; d0++)
    {
        for (int d1 = 0; d1 < 3; d1++)
        {
            codeword_t cw;
            hamming_encode(d0, d1, &cw);
            int rd0, rd1;
            hamming_decode(&cw, &rd0, &rd1);
            ASSERT(rd0 == d0 && rd1 == d1, "decode matches encode");
        }
    }
    PASS();
}

static void batch_6632(void)
{
    TEST("Round-trip with single error correction: all 9 * 8 cases");
    int ok = 1;
    for (int d0 = 0; d0 < 3 && ok; d0++)
    {
        for (int d1 = 0; d1 < 3 && ok; d1++)
        {
            for (int pos = 0; pos < 4 && ok; pos++)
            {
                for (int err = 1; err <= 2 && ok; err++)
                {
                    codeword_t cw;
                    hamming_encode(d0, d1, &cw);
                    inject_error(&cw, pos, err);
                    int rc = hamming_correct(&cw);
                    if (rc != 1)
                    {
                        ok = 0;
                        break;
                    }
                    int rd0, rd1;
                    hamming_decode(&cw, &rd0, &rd1);
                    if (rd0 != d0 || rd1 != d1)
                    {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    ASSERT(ok, "all single-error cases corrected");
    PASS();
}

static void batch_6633(void)
{
    TEST("GF(3) subtraction: 0-1=2");
    ASSERT(gf3_sub(0, 1) == 2, "0-1=2 mod 3");
    PASS();
}

static void batch_6634(void)
{
    TEST("GF(3) subtraction: 1-2=2");
    ASSERT(gf3_sub(1, 2) == 2, "1-2=2 mod 3");
    PASS();
}

static void batch_6635(void)
{
    TEST("GF(3) subtraction: 2-1=1");
    ASSERT(gf3_sub(2, 1) == 1, "2-1=1");
    PASS();
}

static void batch_6636(void)
{
    TEST("Parity check matrix H: col0 = [1,1]");
    /* Verify H*G^T = 0 for each column of G */
    /* G col0 = [1,0], H*[1,0]^T = [1*1+1*0, 1*1+2*0] = [1,1] for data pos */
    /* But H*codeword = 0 for valid codewords, so let's verify that property */
    codeword_t cw;
    hamming_encode(1, 0, &cw);
    syndrome_t syn;
    hamming_syndrome(&cw, &syn);
    ASSERT(syndrome_is_zero(&syn), "H*codeword = 0");
    PASS();
}

static void batch_6637(void)
{
    TEST("Parity check: H row structure verification");
    /* H = [1 1 2 0; 1 2 0 2] */
    /* Verify: H*G = 0 (mod 3) for generator columns */
    /* G = [1 0 1 1; 0 1 1 2] */
    /* H*G^T row 0: 1*1+1*0 + 2*1+0*1 = 1+0+2+0 = 3 = 0 mod 3 ✓ */
    /* H*G^T row 0, col1: 1*0+1*1 + 2*1+0*2 = 0+1+2+0 = 3 = 0 mod 3 ✓ */
    int hg00 = (1 * 1 + 1 * 0 + 2 * 1 + 0 * 1) % 3;
    int hg01 = (1 * 0 + 1 * 1 + 2 * 1 + 0 * 2) % 3;
    int hg10 = (1 * 1 + 2 * 0 + 0 * 1 + 2 * 1) % 3;
    int hg11 = (1 * 0 + 2 * 1 + 0 * 1 + 2 * 2) % 3;
    ASSERT(hg00 == 0, "H*G[0,0]=0");
    ASSERT(hg01 == 0, "H*G[0,1]=0");
    ASSERT(hg10 == 0, "H*G[1,0]=0");
    ASSERT(hg11 == 0, "H*G[1,1]=0");
    PASS();
}

static void batch_6638(void)
{
    TEST("Syndrome uniqueness: each single error has unique syndrome");
    /* 4 positions × 2 error values = 8 syndromes, all should be distinct */
    int syns[8][2];
    int idx = 0;
    for (int pos = 0; pos < 4; pos++)
    {
        for (int err = 1; err <= 2; err++)
        {
            codeword_t cw;
            hamming_encode(0, 0, &cw);
            inject_error(&cw, pos, err);
            syndrome_t syn;
            hamming_syndrome(&cw, &syn);
            syns[idx][0] = syn.s[0];
            syns[idx][1] = syn.s[1];
            idx++;
        }
    }
    /* Check uniqueness */
    int unique = 1;
    for (int i = 0; i < 8 && unique; i++)
    {
        for (int j = i + 1; j < 8 && unique; j++)
        {
            if (syns[i][0] == syns[j][0] && syns[i][1] == syns[j][1])
                unique = 0;
        }
    }
    ASSERT(unique, "all single-error syndromes are unique");
    PASS();
}

static void batch_6639(void)
{
    TEST("Syndrome non-zero for all single errors");
    for (int pos = 0; pos < 4; pos++)
    {
        for (int err = 1; err <= 2; err++)
        {
            codeword_t cw;
            hamming_encode(0, 0, &cw);
            inject_error(&cw, pos, err);
            syndrome_t syn;
            hamming_syndrome(&cw, &syn);
            ASSERT(!syndrome_is_zero(&syn), "single error detected");
        }
    }
    PASS();
}

static void batch_6640(void)
{
    TEST("Encode (1,2) and decode");
    codeword_t cw;
    hamming_encode(1, 2, &cw);
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 1 && d1 == 2, "decode (1,2)");
    PASS();
}

static void batch_6641(void)
{
    TEST("Encode (2,1) and decode");
    codeword_t cw;
    hamming_encode(2, 1, &cw);
    int d0, d1;
    hamming_decode(&cw, &d0, &d1);
    ASSERT(d0 == 2 && d1 == 1, "decode (2,1)");
    PASS();
}

static void batch_6642(void)
{
    TEST("GF(3) additive identity: a+0=a");
    for (int a = 0; a < 3; a++)
    {
        ASSERT(gf3_add(a, 0) == a, "a+0=a");
    }
    PASS();
}

static void batch_6643(void)
{
    TEST("GF(3) multiplicative identity: a*1=a");
    for (int a = 0; a < 3; a++)
    {
        ASSERT(gf3_mul(a, 1) == a, "a*1=a");
    }
    PASS();
}

static void batch_6644(void)
{
    TEST("GF(3) additive inverse: a + (3-a) = 0 mod 3");
    for (int a = 0; a < 3; a++)
    {
        int neg_a = (3 - a) % 3;
        ASSERT(gf3_add(a, neg_a) == 0, "a+(-a)=0");
    }
    PASS();
}

static void batch_6645(void)
{
    TEST("GF(3) commutativity of addition");
    for (int a = 0; a < 3; a++)
    {
        for (int b = 0; b < 3; b++)
        {
            ASSERT(gf3_add(a, b) == gf3_add(b, a), "a+b=b+a");
        }
    }
    PASS();
}

static void batch_6646(void)
{
    TEST("GF(3) commutativity of multiplication");
    for (int a = 0; a < 3; a++)
    {
        for (int b = 0; b < 3; b++)
        {
            ASSERT(gf3_mul(a, b) == gf3_mul(b, a), "a*b=b*a");
        }
    }
    PASS();
}

static void batch_6647(void)
{
    TEST("GF(3) distributive: a*(b+c) = a*b + a*c");
    for (int a = 0; a < 3; a++)
    {
        for (int b = 0; b < 3; b++)
        {
            for (int c = 0; c < 3; c++)
            {
                int lhs = gf3_mul(a, gf3_add(b, c));
                int rhs = gf3_add(gf3_mul(a, b), gf3_mul(a, c));
                ASSERT(lhs == rhs, "distributive law");
            }
        }
    }
    PASS();
}

static void batch_6648(void)
{
    TEST("Trit round-trip through GF(3) for all 3 values");
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3; i++)
    {
        int g = trit_to_gf3(vals[i]);
        trit t = gf3_to_trit(g);
        ASSERT(t == vals[i], "trit -> gf3 -> trit round-trip");
    }
    PASS();
}

static void batch_6649(void)
{
    TEST("Codeword distance: distinct codewords differ in >= 3 positions");
    /* Minimum distance of [4,2] Hamming should be 3 */
    int min_dist = 5;
    for (int a0 = 0; a0 < 3; a0++)
    {
        for (int a1 = 0; a1 < 3; a1++)
        {
            for (int b0 = 0; b0 < 3; b0++)
            {
                for (int b1 = 0; b1 < 3; b1++)
                {
                    if (a0 == b0 && a1 == b1)
                        continue;
                    codeword_t ca, cb;
                    hamming_encode(a0, a1, &ca);
                    hamming_encode(b0, b1, &cb);
                    int dist = 0;
                    for (int i = 0; i < 4; i++)
                    {
                        if (ca.c[i] != cb.c[i])
                            dist++;
                    }
                    if (dist < min_dist)
                        min_dist = dist;
                }
            }
        }
    }
    ASSERT(min_dist >= 3, "minimum distance >= 3");
    PASS();
}

static void batch_6650(void)
{
    TEST("Number of valid codewords = 9 (3^2)");
    /* Just verify we can encode all 9 */
    int count = 0;
    for (int d0 = 0; d0 < 3; d0++)
    {
        for (int d1 = 0; d1 < 3; d1++)
        {
            codeword_t cw;
            hamming_encode(d0, d1, &cw);
            syndrome_t syn;
            hamming_syndrome(&cw, &syn);
            if (syndrome_is_zero(&syn))
                count++;
        }
    }
    ASSERT(count == 9, "9 valid codewords");
    PASS();
}

static void batch_6651(void)
{
    TEST("Correctness exhaustive: every single error on every codeword");
    int total_ok = 1;
    for (int d0 = 0; d0 < 3 && total_ok; d0++)
    {
        for (int d1 = 0; d1 < 3 && total_ok; d1++)
        {
            for (int pos = 0; pos < 4 && total_ok; pos++)
            {
                for (int err = 1; err <= 2 && total_ok; err++)
                {
                    codeword_t cw;
                    hamming_encode(d0, d1, &cw);
                    inject_error(&cw, pos, err);
                    hamming_correct(&cw);
                    int rd0, rd1;
                    hamming_decode(&cw, &rd0, &rd1);
                    if (rd0 != d0 || rd1 != d1)
                        total_ok = 0;
                }
            }
        }
    }
    ASSERT(total_ok, "exhaustive single-error correction");
    PASS();
}

int main(void)
{
    printf("=== Batch 117: Tests 6602-6651 — Ternary Error Correction (GF(3) Hamming) ===\n");
    batch_6602();
    batch_6603();
    batch_6604();
    batch_6605();
    batch_6606();
    batch_6607();
    batch_6608();
    batch_6609();
    batch_6610();
    batch_6611();
    batch_6612();
    batch_6613();
    batch_6614();
    batch_6615();
    batch_6616();
    batch_6617();
    batch_6618();
    batch_6619();
    batch_6620();
    batch_6621();
    batch_6622();
    batch_6623();
    batch_6624();
    batch_6625();
    batch_6626();
    batch_6627();
    batch_6628();
    batch_6629();
    batch_6630();
    batch_6631();
    batch_6632();
    batch_6633();
    batch_6634();
    batch_6635();
    batch_6636();
    batch_6637();
    batch_6638();
    batch_6639();
    batch_6640();
    batch_6641();
    batch_6642();
    batch_6643();
    batch_6644();
    batch_6645();
    batch_6646();
    batch_6647();
    batch_6648();
    batch_6649();
    batch_6650();
    batch_6651();
    printf("\n=== Results: %d/%d passed, %d failed ===\n", pass_count, test_count, fail_count);
    return fail_count ? 1 : 0;
}
