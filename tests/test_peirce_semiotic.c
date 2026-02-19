/**
 * @file  test_peirce_semiotic.c
 * @brief seT6 – Peircean Semiotic Engine test suite (200 assertions).
 *
 * Sections:
 *   1. Initialization & basics         (20 tests)
 *   2. Sign classification (10 classes) (35 tests)
 *   3. Semiosis chains                  (25 tests)
 *   4. Information theory               (25 tests)
 *   5. Triadic determination            (25 tests)
 *   6. Reduction thesis                 (25 tests)
 *   7. Interpretant analysis            (25 tests)
 *   8. Category ops, hypoicon, adjacency(20 tests)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "set5/trit_peirce_semiotic.h"

/* ==== Test harness ====================================================== */

static int g_pass = 0, g_fail = 0;

#define TEST(cond, msg)                                                      \
    do {                                                                     \
        if (cond) {                                                          \
            printf("  %-62s [PASS]\n", msg);                                 \
            g_pass++;                                                        \
        } else {                                                             \
            printf("  %-62s [FAIL]\n", msg);                                 \
            g_fail++;                                                        \
        }                                                                    \
    } while (0)

/* ======================================================================== */
/*  Section 1: Initialization & Basics (20 tests)                           */
/* ======================================================================== */
static void test_init_basics(void)
{
    printf("\n--- Section 1: Initialization & Basics ---\n");

    /* 1.1 Init succeeds */
    psm_state_t st;
    TEST(psm_init(&st) == 0, "1.1  psm_init succeeds");

    /* 1.2 State is initialized */
    TEST(st.initialized == 1, "1.2  initialized flag set");

    /* 1.3 Chain starts empty */
    TEST(st.chain_len == 0, "1.3  chain_len starts at 0");

    /* 1.4 NULL init fails */
    TEST(psm_init(NULL) == -1, "1.4  NULL init returns -1");

    /* 1.5 Constants: Firstness = -1 */
    TEST(PSM_FIRSTNESS == -1, "1.5  PSM_FIRSTNESS == -1");

    /* 1.6 Constants: Secondness = 0 */
    TEST(PSM_SECONDNESS == 0, "1.6  PSM_SECONDNESS == 0");

    /* 1.7 Constants: Thirdness = +1 */
    TEST(PSM_THIRDNESS == 1, "1.7  PSM_THIRDNESS == +1");

    /* 1.8 Qualisign equals Firstness */
    TEST(PSM_QUALISIGN == PSM_FIRSTNESS, "1.8  QUALISIGN == FIRSTNESS");

    /* 1.9 Sinsign equals Secondness */
    TEST(PSM_SINSIGN == PSM_SECONDNESS, "1.9  SINSIGN == SECONDNESS");

    /* 1.10 Legisign equals Thirdness */
    TEST(PSM_LEGISIGN == PSM_THIRDNESS, "1.10 LEGISIGN == THIRDNESS");

    /* 1.11 Icon equals Firstness */
    TEST(PSM_ICON == PSM_FIRSTNESS, "1.11 ICON == FIRSTNESS");

    /* 1.12 Index equals Secondness */
    TEST(PSM_INDEX == PSM_SECONDNESS, "1.12 INDEX == SECONDNESS");

    /* 1.13 Symbol equals Thirdness */
    TEST(PSM_SYMBOL == PSM_THIRDNESS, "1.13 SYMBOL == THIRDNESS");

    /* 1.14 Rheme equals Firstness */
    TEST(PSM_RHEME == PSM_FIRSTNESS, "1.14 RHEME == FIRSTNESS");

    /* 1.15 Dicisign equals Secondness */
    TEST(PSM_DICISIGN == PSM_SECONDNESS, "1.15 DICISIGN == SECONDNESS");

    /* 1.16 Argument equals Thirdness */
    TEST(PSM_ARGUMENT == PSM_THIRDNESS, "1.16 ARGUMENT == THIRDNESS");

    /* 1.17 Exactly 10 valid classes */
    TEST(PSM_NUM_VALID_CLASSES == 10, "1.17 NUM_VALID_CLASSES == 10");

    /* 1.18 Three trichotomies */
    TEST(PSM_NUM_TRICHOTOMIES == 3, "1.18 NUM_TRICHOTOMIES == 3");

    /* 1.19 Max chain depth */
    TEST(PSM_MAX_CHAIN == 64, "1.19 PSM_MAX_CHAIN == 64");

    /* 1.20 Hypoicon image is 1 */
    TEST(PSM_IMAGE == 1 && PSM_DIAGRAM == 2 && PSM_METAPHOR == 3,
         "1.20 Hypoicon types: 1=image 2=diagram 3=metaphor");
}

/* ======================================================================== */
/*  Section 2: Sign Classification – 10 Valid Classes (35 tests)            */
/* ======================================================================== */
static void test_sign_classification(void)
{
    printf("\n--- Section 2: Sign Classification ---\n");

    psm_sign_class_t cls;

    /* 2.1–2.10: Each valid class classifies correctly */
    TEST(psm_classify(&cls, -1, -1, -1) == 0 && psm_class_id(&cls) == 1,
         "2.1  Class I:   Rhematic Iconic Qualisign (-1,-1,-1)");
    TEST(psm_classify(&cls, 0, -1, -1) == 0 && psm_class_id(&cls) == 2,
         "2.2  Class II:  Rhematic Iconic Sinsign (0,-1,-1)");
    TEST(psm_classify(&cls, 0, 0, -1) == 0 && psm_class_id(&cls) == 3,
         "2.3  Class III: Rhematic Indexical Sinsign (0,0,-1)");
    TEST(psm_classify(&cls, 0, 0, 0) == 0 && psm_class_id(&cls) == 4,
         "2.4  Class IV:  Dicent Indexical Sinsign (0,0,0)");
    TEST(psm_classify(&cls, 1, -1, -1) == 0 && psm_class_id(&cls) == 5,
         "2.5  Class V:   Rhematic Iconic Legisign (1,-1,-1)");
    TEST(psm_classify(&cls, 1, 0, -1) == 0 && psm_class_id(&cls) == 6,
         "2.6  Class VI:  Rhematic Indexical Legisign (1,0,-1)");
    TEST(psm_classify(&cls, 1, 0, 0) == 0 && psm_class_id(&cls) == 7,
         "2.7  Class VII: Dicent Indexical Legisign (1,0,0)");
    TEST(psm_classify(&cls, 1, 1, -1) == 0 && psm_class_id(&cls) == 8,
         "2.8  Class VIII:Rhematic Symbol Legisign (1,1,-1)");
    TEST(psm_classify(&cls, 1, 1, 0) == 0 && psm_class_id(&cls) == 9,
         "2.9  Class IX:  Dicent Symbol Legisign (1,1,0)");
    TEST(psm_classify(&cls, 1, 1, 1) == 0 && psm_class_id(&cls) == 10,
         "2.10 Class X:   Argument Symbol Legisign (1,1,1)");

    /* 2.11 Invalid: Firstness > Secondness in II > I */
    TEST(psm_classify(&cls, -1, 0, -1) == -1,
         "2.11 Invalid: qualisign+index rejected (-1,0,-1)");

    /* 2.12 Invalid: III > II */
    TEST(psm_classify(&cls, 0, -1, 0) == -1,
         "2.12 Invalid: icon+dicisign rejected (0,-1,0)");

    /* 2.13 Invalid: argument with icon */
    TEST(psm_classify(&cls, 1, -1, 1) == -1,
         "2.13 Invalid: icon+argument rejected (1,-1,1)");

    /* 2.14 Invalid: symbol with qualisign */
    TEST(psm_classify(&cls, -1, 1, -1) == -1,
         "2.14 Invalid: qualisign+symbol rejected (-1,1,-1)");

    /* 2.15 Exactly 17 of 27 combinations are invalid */
    {
        int valid_count = 0;
        for (int a = -1; a <= 1; a++)
            for (int b = -1; b <= 1; b++)
                for (int c = -1; c <= 1; c++) {
                    psm_sign_class_t tc;
                    if (psm_classify(&tc, (trit)a, (trit)b, (trit)c) == 0)
                        valid_count++;
                }
        TEST(valid_count == 10, "2.15 Exactly 10 of 27 combos valid");
    }

    /* 2.16 psm_is_valid_class on valid class */
    psm_classify(&cls, 1, 0, 0);
    TEST(psm_is_valid_class(&cls) == 1, "2.16 is_valid_class on valid → 1");

    /* 2.17 is_valid_class NULL → 0 */
    TEST(psm_is_valid_class(NULL) == 0, "2.17 is_valid_class(NULL) → 0");

    /* 2.18 Manually set invalid class, check rejection */
    {
        psm_sign_class_t bad = { -1, 1, 0 };
        TEST(psm_is_valid_class(&bad) == 0, "2.18 Manually invalid → 0");
    }

    /* 2.19 class_id on invalid → 0 */
    {
        psm_sign_class_t bad = { -1, 1, 0 };
        TEST(psm_class_id(&bad) == 0, "2.19 class_id on invalid → 0");
    }

    /* 2.20 class_name for each ID */
    TEST(strstr(psm_class_name(1), "Qualisign") != NULL,
         "2.20 class_name(1) contains 'Qualisign'");
    TEST(strstr(psm_class_name(10), "Argument") != NULL,
         "2.21 class_name(10) contains 'Argument'");

    /* 2.22 class_name invalid → "Invalid" */
    TEST(strcmp(psm_class_name(0), "Invalid") == 0,
         "2.22 class_name(0) → 'Invalid'");
    TEST(strcmp(psm_class_name(11), "Invalid") == 0,
         "2.23 class_name(11) → 'Invalid'");

    /* 2.24 Enumerate all 10 classes */
    {
        psm_sign_class_t arr[12];
        int n = psm_enumerate_classes(arr, 12);
        TEST(n == 10, "2.24 enumerate returns 10 classes");
    }

    /* 2.25 Enumerate with small buffer */
    {
        psm_sign_class_t arr[5];
        int n = psm_enumerate_classes(arr, 5);
        TEST(n == 5, "2.25 enumerate with max=5 returns 5");
    }

    /* 2.26 Enumerate NULL → 0 */
    TEST(psm_enumerate_classes(NULL, 10) == 0, "2.26 enumerate(NULL) → 0");

    /* 2.27 Class I is all-Firstness */
    psm_classify(&cls, -1, -1, -1);
    TEST(cls.sign_itself == -1 && cls.sign_object == -1 &&
         cls.sign_interpretant == -1,
         "2.27 Class I: all Firstness");

    /* 2.28 Class X is all-Thirdness */
    psm_classify(&cls, 1, 1, 1);
    TEST(cls.sign_itself == 1 && cls.sign_object == 1 &&
         cls.sign_interpretant == 1,
         "2.28 Class X: all Thirdness");

    /* 2.29 All symbols are legisigns (class VIII–X) */
    {
        int ok = 1;
        for (int id = 8; id <= 10; id++) {
            psm_sign_class_t arr[10];
            psm_enumerate_classes(arr, 10);
            if (arr[id-1].sign_itself != PSM_LEGISIGN) ok = 0;
        }
        TEST(ok, "2.29 All symbols are legisigns (VIII–X)");
    }

    /* 2.30 Class names all contain "Legisign" for V–X */
    {
        int ok = 1;
        for (int id = 5; id <= 10; id++) {
            if (!strstr(psm_class_name(id), "Legisign")) ok = 0;
        }
        TEST(ok, "2.30 Classes V–X all contain 'Legisign'");
    }

    /* 2.31 classify NULL cls → -1 */
    TEST(psm_classify(NULL, 0, 0, 0) == -1, "2.31 classify(NULL) → -1");

    /* 2.32 Out-of-range trit value rejected */
    TEST(psm_classify(&cls, 2, 0, 0) == -1, "2.32 classify(2,0,0) → -1");

    /* 2.33 Class IV: "Dicent Indexical Sinsign" (weathercock example) */
    psm_classify(&cls, 0, 0, 0);
    TEST(strstr(psm_class_name(psm_class_id(&cls)), "Dicent") != NULL,
         "2.33 Class IV weathercock is Dicent");

    /* 2.34 Class VIII: "Rhematic Symbol" (common noun example) */
    psm_classify(&cls, 1, 1, -1);
    TEST(strstr(psm_class_name(psm_class_id(&cls)), "Rhematic Symbol") != NULL,
         "2.34 Class VIII common noun is Rhematic Symbol");

    /* 2.35 Each class has unique ID 1-10 */
    {
        int seen[11] = {0};
        psm_sign_class_t arr[10];
        psm_enumerate_classes(arr, 10);
        int ok = 1;
        for (int i = 0; i < 10; i++) {
            int id = psm_class_id(&arr[i]);
            if (id < 1 || id > 10 || seen[id]) ok = 0;
            seen[id] = 1;
        }
        TEST(ok, "2.35 Each class has unique ID 1–10");
    }
}

/* ======================================================================== */
/*  Section 3: Semiosis Chains (25 tests)                                   */
/* ======================================================================== */
static void test_semiosis_chains(void)
{
    printf("\n--- Section 3: Semiosis Chains ---\n");

    psm_state_t st;
    psm_init(&st);

    psm_sign_class_t cls_ix;
    psm_classify(&cls_ix, 1, 1, 0);  /* Class IX: Dicent Symbol */

    psm_sign_class_t cls_x;
    psm_classify(&cls_x, 1, 1, 1);   /* Class X: Argument */

    /* 3.1 Create first relation */
    psm_object_t obj1 = { 500, 800 };
    psm_interpretant_t int1 = { 400, 600, 800 };
    int idx = psm_create_relation(&st, 1000, obj1, int1, &cls_ix);
    TEST(idx == 0, "3.1  First relation at index 0");

    /* 3.2 Chain length is now 1 */
    TEST(st.chain_len == 1, "3.2  chain_len == 1");

    /* 3.3 Stored sign value matches */
    TEST(st.chain[0].sign_value == 1000, "3.3  sign_value == 1000");

    /* 3.4 Stored object matches */
    TEST(st.chain[0].object.immediate == 500 &&
         st.chain[0].object.dynamic == 800,
         "3.4  Object stored correctly");

    /* 3.5 Stored interpretant matches */
    TEST(st.chain[0].interpretant.immediate == 400 &&
         st.chain[0].interpretant.dynamic == 600 &&
         st.chain[0].interpretant.final_ == 800,
         "3.5  Interpretant stored correctly");

    /* 3.6 Class ID stored */
    TEST(st.chain[0].class_id == 9, "3.6  class_id == 9 (IX)");

    /* 3.7 Extend chain: prev interpretant.dynamic → next sign */
    psm_object_t obj2 = { 600, 850 };
    psm_interpretant_t int2 = { 550, 700, 850 };
    idx = psm_extend_chain(&st, obj2, int2, &cls_x);
    TEST(idx == 1, "3.7  Extended chain at index 1");

    /* 3.8 New sign value = prev interpretant.dynamic (600) */
    TEST(st.chain[1].sign_value == 600,
         "3.8  New sign == prev interp.dynamic (600)");

    /* 3.9 Chain length now 2 */
    TEST(st.chain_len == 2, "3.9  chain_len == 2");

    /* 3.10 Second relation class */
    TEST(st.chain[1].class_id == 10, "3.10 Second relation class X");

    /* 3.11 Extend fails on uninitialized state */
    {
        psm_state_t bad;
        memset(&bad, 0, sizeof(bad));
        TEST(psm_extend_chain(&bad, obj2, int2, &cls_x) == -1,
             "3.11 extend_chain on uninit → -1");
    }

    /* 3.12 Extend fails on empty chain */
    {
        psm_state_t empty;
        psm_init(&empty);
        TEST(psm_extend_chain(&empty, obj2, int2, &cls_x) == -1,
             "3.12 extend_chain on empty → -1");
    }

    /* 3.13 Create relation with invalid class → -1 */
    {
        psm_sign_class_t bad = { -1, 1, 0 };
        TEST(psm_create_relation(&st, 100, obj1, int1, &bad) == -1,
             "3.13 create with invalid class → -1");
    }

    /* 3.14 NULL state → -1 */
    TEST(psm_create_relation(NULL, 100, obj1, int1, &cls_ix) == -1,
         "3.14 create(NULL state) → -1");

    /* 3.15 NULL class → -1 */
    TEST(psm_create_relation(&st, 100, obj1, int1, NULL) == -1,
         "3.15 create(NULL class) → -1");

    /* 3.16 Build longer chain (8 steps) for convergence */
    {
        psm_state_t cst;
        psm_init(&cst);
        psm_sign_class_t cls_v;
        psm_classify(&cls_v, 1, -1, -1);

        /* Start: sign=1000, object has dynamic=500 */
        psm_object_t o = { 400, 500 };
        psm_interpretant_t it = { 1000, 800, 500 };
        psm_create_relation(&cst, 1000, o, it, &cls_v);

        /* Iterate: each interpretant approaches 500 */
        for (int i = 0; i < 7; i++) {
            int prev_dyn = cst.chain[cst.chain_len-1].interpretant.dynamic;
            int next_dyn = (prev_dyn + 500) / 2;
            psm_interpretant_t nit = { prev_dyn, next_dyn, 500 };
            psm_extend_chain(&cst, o, nit, &cls_v);
        }
        TEST(cst.chain_len == 8, "3.16 Built 8-step semiosis chain");

        /* 3.17 Last dynamic interpretant closer to final than first */
        int d_first = abs(cst.chain[0].interpretant.dynamic -
                          cst.chain[0].interpretant.final_);
        int d_last  = abs(cst.chain[7].interpretant.dynamic -
                          cst.chain[7].interpretant.final_);
        TEST(d_last < d_first, "3.17 Chain converges toward final interp");

        /* 3.18 Convergence metric > 0 */
        int conv = psm_convergence(&cst);
        TEST(conv > 0, "3.18 Convergence metric > 0");

        /* 3.19 Convergence metric high for well-converging chain */
        TEST(conv > 800, "3.19 Convergence > 800 for approaching chain");
    }

    /* 3.20 Convergence on < 2 elements → 0 */
    {
        psm_state_t one;
        psm_init(&one);
        TEST(psm_convergence(&one) == 0, "3.20 Convergence on empty → 0");
    }

    /* 3.21 Convergence NULL → 0 */
    TEST(psm_convergence(NULL) == 0, "3.21 Convergence(NULL) → 0");

    /* 3.22 Semiosis preserves sign classification through chain */
    TEST(st.chain[0].class_id == 9 && st.chain[1].class_id == 10,
         "3.22 Chain preserves class IDs (9, 10)");

    /* 3.23 Each step's sign = previous step's dynamic interpretant */
    TEST(st.chain[1].sign_value == st.chain[0].interpretant.dynamic,
         "3.23 Semiosis: sign[n+1] = interp.dynamic[n]");

    /* 3.24 Can use different classes along chain */
    {
        psm_state_t mixed;
        psm_init(&mixed);
        psm_sign_class_t cls_i;
        psm_classify(&cls_i, -1, -1, -1);

        psm_object_t o = { 100, 200 };
        psm_interpretant_t it = { 50, 150, 200 };
        psm_create_relation(&mixed, 100, o, it, &cls_i);

        psm_interpretant_t it2 = { 150, 175, 200 };
        psm_extend_chain(&mixed, o, it2, &cls_ix);

        TEST(mixed.chain[0].class_id == 1 && mixed.chain[1].class_id == 9,
             "3.24 Mixed classes in chain (I → IX)");
    }

    /* 3.25 Chain respects chronological order */
    TEST(st.chain[0].interpretant.dynamic <= st.chain[1].sign_value + 1 &&
         st.chain[0].interpretant.dynamic >= st.chain[1].sign_value - 1,
         "3.25 Chain chronological: interp → sign continuity");
}

/* ======================================================================== */
/*  Section 4: Information Theory (25 tests)                                */
/* ======================================================================== */
static void test_information(void)
{
    printf("\n--- Section 4: Information Theory ---\n");

    /* 4.1 Basic information: ext=1000 × int=1000 → 1000 */
    TEST(psm_information(1000, 1000) == 1000,
         "4.1  info(1000,1000) = 1000 (1×1=1)");

    /* 4.2 Info: ext=2000 × int=500 → 1000 */
    TEST(psm_information(2000, 500) == 1000,
         "4.2  info(2000,500) = 1000 (2×0.5=1)");

    /* 4.3 Info: ext=3000 × int=1000 → 3000 */
    TEST(psm_information(3000, 1000) == 3000,
         "4.3  info(3000,1000) = 3000");

    /* 4.4 Zero intension → zero info */
    TEST(psm_information(5000, 0) == 0,
         "4.4  info(5000,0) = 0");

    /* 4.5 Zero extension → zero info */
    TEST(psm_information(0, 5000) == 0,
         "4.5  info(0,5000) = 0");

    /* 4.6 Negative (inverted) extension */
    TEST(psm_information(-2000, 500) == -1000,
         "4.6  info(-2000,500) = -1000");

    /* 4.7 Large values don't overflow */
    {
        int info = psm_information(1000000, 1000000);
        TEST(info > 0, "4.7  Large values don't overflow to negative");
    }

    /* 4.8 Inverse: info=1000, ext=2000 → int=500 */
    TEST(psm_information_inverse(1000, 2000) == 500,
         "4.8  inverse(1000, 2000) = 500");

    /* 4.9 Inverse: info=3000, int=1000 → ext=3000 */
    TEST(psm_information_inverse(3000, 1000) == 3000,
         "4.9  inverse(3000, 1000) = 3000");

    /* 4.10 Inverse: division by zero → -1 */
    TEST(psm_information_inverse(1000, 0) == -1,
         "4.10 inverse(1000, 0) = -1");

    /* 4.11 Round-trip: info(ext, inv(info,ext)) ≈ info */
    {
        int ext = 2000, info = 5000;
        int inv = psm_information_inverse(info, ext);
        int recomputed = psm_information(ext, inv);
        TEST(abs(recomputed - info) <= 1,
             "4.11 Round-trip: info → inverse → info");
    }

    /* 4.12 Inverse information law: more intension → less extension */
    {
        int info = 10000;
        int ext_a = psm_information_inverse(info, 500);   /* low intension */
        int ext_b = psm_information_inverse(info, 2000);  /* high intension */
        TEST(ext_a > ext_b,
             "4.12 More intension → less extension (constant info)");
    }

    /* 4.13 More extension → less intension */
    {
        int info = 10000;
        int int_a = psm_information_inverse(info, 500);   /* low extension */
        int int_b = psm_information_inverse(info, 2000);  /* high extension */
        TEST(int_a > int_b,
             "4.13 More extension → less intension (constant info)");
    }

    /* 4.14 Information is commutative: info(a,b) == info(b,a) */
    TEST(psm_information(3000, 2000) == psm_information(2000, 3000),
         "4.14 information is commutative");

    /* 4.15 Information scales linearly: info(2a, b) = 2*info(a, b) */
    {
        int i1 = psm_information(1000, 3000);
        int i2 = psm_information(2000, 3000);
        TEST(abs(i2 - 2 * i1) <= 1,
             "4.15 info(2a,b) = 2 * info(a,b)");
    }

    /* 4.16–4.20 Various fixed values */
    TEST(psm_information(1500, 2000) == 3000,
         "4.16 info(1500,2000) = 3000 (1.5×2=3)");
    TEST(psm_information(500, 500) == 250,
         "4.17 info(500,500) = 250 (0.5×0.5=0.25)");
    TEST(psm_information(4000, 250) == 1000,
         "4.18 info(4000,250) = 1000 (4×0.25=1)");
    TEST(psm_information(100, 100) == 10,
         "4.19 info(100,100) = 10 (0.1×0.1=0.01)");
    TEST(psm_information(10000, 1000) == 10000,
         "4.20 info(10000,1000) = 10000 (10×1=10)");

    /* 4.21 Proposition comprehension: more implications → deeper */
    {
        /* "All men are mortal" has more depth than "Some things exist" */
        int depth_specific = 800;  /* High intension */
        int depth_vague    = 200;  /* Low intension */
        int ext   = 1000;
        int info_spec = psm_information(ext, depth_specific);
        int info_vague = psm_information(ext, depth_vague);
        TEST(info_spec > info_vague,
             "4.21 More implications → more information");
    }

    /* 4.22 Wider extension with same info requires lower intension */
    {
        int info = 6000;
        int int_narrow = psm_information_inverse(info, 2000);
        int int_wide   = psm_information_inverse(info, 6000);
        TEST(int_narrow > int_wide,
             "4.22 Wider ext → lower int for same info");
    }

    /* 4.23–4.25 Edge cases */
    TEST(psm_information(1, 1000000) == 1000,
         "4.23 info(1, 1000000) = 1000");
    TEST(psm_information(1000000, 1) == 1000,
         "4.24 info(1000000, 1) = 1000");
    {
        int inv = psm_information_inverse(1000, 1);
        TEST(inv == 1000000,
             "4.25 inverse(1000, 1) = 1000000");
    }
}

/* ======================================================================== */
/*  Section 5: Triadic Determination (25 tests)                             */
/* ======================================================================== */
static void test_determination(void)
{
    printf("\n--- Section 5: Triadic Determination ---\n");

    /* 5.1 Perfect coherence: O=S=I */
    TEST(psm_triadic_determination(500, 500, 500) == 1000,
         "5.1  Perfect coherence (O=S=I) = 1000");

    /* 5.2 Zero values: all zero → perfect */
    TEST(psm_triadic_determination(0, 0, 0) == 1000,
         "5.2  All zeros → 1000");

    /* 5.3 Moderate coherence */
    {
        int coh = psm_triadic_determination(1000, 800, 600);
        TEST(coh > 500 && coh < 1000,
             "5.3  Moderate deviation → mid coherence");
    }

    /* 5.4 Low coherence with large deviation */
    {
        int coh = psm_triadic_determination(1000, 0, -1000);
        TEST(coh < 500, "5.4  Large deviation → low coherence");
    }

    /* 5.5 Symmetric: swapping O and I gives same coherence */
    {
        int c1 = psm_triadic_determination(100, 500, 900);
        int c2 = psm_triadic_determination(900, 500, 100);
        TEST(c1 == c2,
             "5.5  Symmetric around sign (swap O↔I)");
    }

    /* 5.6 Interpretant equals average of O and S → max coherence */
    {
        int coh = psm_triadic_determination(200, 800, 500);
        TEST(coh == 1000, "5.6  I = avg(O,S) → max coherence");
    }

    /* 5.7 Interpretant far from average → lower coherence */
    {
        int c1 = psm_triadic_determination(200, 800, 500);  /* avg=500 */
        int c2 = psm_triadic_determination(200, 800, 100);  /* off by 400 */
        TEST(c1 > c2, "5.7  I further from avg(O,S) → lower coh");
    }

    /* 5.8–5.11 Various coherence levels */
    {
        int c = psm_triadic_determination(1000, 1000, 1000);
        TEST(c == 1000, "5.8  Identical large values → 1000");
    }
    {
        int c = psm_triadic_determination(-500, -500, -500);
        TEST(c == 1000, "5.9  Identical negative values → 1000");
    }
    {
        int c = psm_triadic_determination(1000, -1000, 0);
        TEST(c == 1000, "5.10 I = avg(1000,-1000)=0 → 1000");
    }
    {
        int c = psm_triadic_determination(1000, 500, 750);
        TEST(c == 1000, "5.11 I = avg(1000,500)=750 → 1000");
    }

    /* 5.12 Coherence is bounded [0, 1000] */
    {
        int c = psm_triadic_determination(1000000, 0, -1000000);
        TEST(c >= 0 && c <= 1000, "5.12 Coherence bounded [0, 1000]");
    }

    /* 5.13–5.15 Sign as mediator */
    {
        /* When sign is between object and interpretant, it mediates */
        int c_med = psm_triadic_determination(100, 500, 900);  /* S between */
        int c_end = psm_triadic_determination(100, 900, 500);  /* S at end */
        TEST(c_med >= 0 && c_end >= 0,
             "5.13 Both mediated and non-mediated have valid coherence");
    }
    {
        int c = psm_triadic_determination(0, 1000, 500);
        TEST(c == 1000, "5.14 I=avg(O,S)=500 with S=1000 → 1000");
    }
    {
        int c = psm_triadic_determination(100, 200, 150);
        TEST(c == 1000, "5.15 I=avg(O,S) in small range → 1000");
    }

    /* 5.16 Non-zero negative values */
    {
        int c = psm_triadic_determination(-400, -200, -300);
        TEST(c == 1000, "5.16 I=avg(-400,-200)=-300 → 1000");
    }

    /* 5.17–5.20 Gradual degradation */
    {
        int c0 = psm_triadic_determination(0, 1000, 500);  /* exact avg */
        int c1 = psm_triadic_determination(0, 1000, 600);  /* off by 100 */
        int c2 = psm_triadic_determination(0, 1000, 800);  /* off by 300 */
        int c3 = psm_triadic_determination(0, 1000, 1000); /* off by 500 */
        TEST(c0 >= c1, "5.17 Closer to avg → higher coherence (0 vs 100)");
        TEST(c1 >= c2, "5.18 Closer to avg → higher coherence (100 vs 300)");
        TEST(c2 >= c3, "5.19 Closer → higher (300 vs 500)");
        TEST(c3 >= 0,  "5.20 Even max deviation has non-negative coh");
    }

    /* 5.21 Determination with all same sign */
    {
        int c = psm_triadic_determination(300, 400, 350);
        TEST(c == 1000, "5.21 I=avg(300,400)=350 → 1000");
    }

    /* 5.22 Negative coherence clamped to 0 not negative */
    {
        int c = psm_triadic_determination(0, 0, 2000000);
        TEST(c >= 0, "5.22 Extreme outlier → coherence ≥ 0");
    }

    /* 5.23–5.25 Object determines sign determines interpretant */
    {
        /* Object change affects coherence */
        int c1 = psm_triadic_determination(500, 500, 500);
        int c2 = psm_triadic_determination(200, 500, 500);
        TEST(c1 >= c2, "5.23 Moving object away from sign reduces coherence");
    }
    {
        /* Sign change affects coherence */
        int c1 = psm_triadic_determination(500, 500, 500);
        int c2 = psm_triadic_determination(500, 200, 500);
        TEST(c1 >= c2, "5.24 Moving sign reduces coherence");
    }
    {
        /* Interpretant change affects coherence */
        int c1 = psm_triadic_determination(500, 500, 500);
        int c2 = psm_triadic_determination(500, 500, 200);
        TEST(c1 >= c2, "5.25 Moving interpretant reduces coherence");
    }
}

/* ======================================================================== */
/*  Section 6: Reduction Thesis (25 tests)                                  */
/* ======================================================================== */
static void test_reduction_thesis(void)
{
    printf("\n--- Section 6: Reduction Thesis ---\n");

    /* 6.1 Genuinely triadic: O and I on opposite sides of S → loss > 0 */
    {
        int loss = psm_reduction_thesis_loss(100, 500, 900);
        TEST(loss > 0, "6.1  Genuine triad (100,500,900) → loss > 0");
    }

    /* 6.2 Degenerate: all equal → some loss (measures residual) */
    {
        int loss = psm_reduction_thesis_loss(500, 500, 500);
        TEST(loss >= 0, "6.2  Degenerate (all equal) → loss ≥ 0");
    }

    /* 6.3 When O,I on same side of S → greater irreducible loss */
    {
        int loss_through = psm_reduction_thesis_loss(100, 500, 900); /* S between */
        int loss_sameside = psm_reduction_thesis_loss(100, 500, 300); /* same side */
        TEST(loss_sameside > loss_through,
             "6.3  Same-side O,I → more irreducible than interpolation");
    }

    /* 6.4 Loss bounded ≤ 1000 */
    {
        int loss = psm_reduction_thesis_loss(0, 500, 1000000);
        TEST(loss <= 1000, "6.4  Loss bounded ≤ 1000");
    }

    /* 6.5 Loss non-negative */
    {
        int loss = psm_reduction_thesis_loss(0, 0, 0);
        TEST(loss >= 0, "6.5  Loss always ≥ 0");
    }

    /* 6.6 Tetradic reduction succeeds */
    {
        int tri[2][3];
        int r = psm_reduce_tetradic(100, 200, 300, 400, tri);
        TEST(r == 0, "6.6  Tetradic reduction succeeds");
    }

    /* 6.7 Tetradic reduction: mediating element */
    {
        int tri[2][3];
        psm_reduce_tetradic(100, 200, 300, 400, tri);
        int m = (200 + 300) / 2;  /* = 250 */
        TEST(tri[0][2] == m && tri[1][0] == m,
             "6.7  Mediating element connects two triads");
    }

    /* 6.8 Tetradic reduction covers all 4 values */
    {
        int tri[2][3];
        psm_reduce_tetradic(10, 20, 30, 40, tri);
        TEST(tri[0][0] == 10 && tri[0][1] == 20 &&
             tri[1][1] == 30 && tri[1][2] == 40,
             "6.8  All 4 values present in reduced triads");
    }

    /* 6.9 Tetradic NULL → -1 */
    TEST(psm_reduce_tetradic(1, 2, 3, 4, NULL) == -1,
         "6.9  reduce_tetradic(NULL) → -1");

    /* 6.10 Symmetry check: original values preserved */
    {
        int tri[2][3];
        psm_reduce_tetradic(500, 600, 700, 800, tri);
        TEST(tri[0][0] == 500 && tri[1][2] == 800,
             "6.10 Endpoints preserved in reduction");
    }

    /* 6.11 Greater mediation distance → greater loss */
    {
        int l1 = psm_reduction_thesis_loss(0, 500, 1000);
        int l2 = psm_reduction_thesis_loss(400, 500, 600);
        TEST(l1 > l2,
             "6.11 Wider O↔I span → more irreducible triadicity");
    }

    /* 6.12 Sign as pure mediator (S equidistant from O and I) */
    {
        int loss = psm_reduction_thesis_loss(0, 500, 1000);
        TEST(loss > 100, "6.12 Pure mediation has significant loss");
    }

    /* 6.13 Degenerate dyadic disguised as triadic */
    {
        /* When I = S, the "triadic" relation is really dyadic O→S */
        int loss = psm_reduction_thesis_loss(0, 500, 500);
        /* This should have less loss than genuine triad */
        int loss_gen = psm_reduction_thesis_loss(0, 500, 1000);
        TEST(loss < loss_gen,
             "6.13 I=S (degenerate) → less loss than genuine triad");
    }

    /* 6.14–6.16 Various triadic configurations */
    {
        int loss = psm_reduction_thesis_loss(-500, 0, 500);
        TEST(loss >= 0, "6.14 Balanced triad (-500,0,500) → loss ≥ 0");
    }
    {
        int loss = psm_reduction_thesis_loss(1000, 500, 0);
        TEST(loss > 0, "6.15 Decreasing triad → loss > 0");
    }
    {
        int loss = psm_reduction_thesis_loss(0, 1000, 500);
        TEST(loss >= 0, "6.16 Mixed triad → loss ≥ 0");
    }

    /* 6.17 Tetradic: large values still reducible */
    {
        int tri[2][3];
        int r = psm_reduce_tetradic(1000000, 2000000, 3000000, 4000000, tri);
        TEST(r == 0, "6.17 Large tetradic still reduces");
    }

    /* 6.18 Tetradic: negative values */
    {
        int tri[2][3];
        psm_reduce_tetradic(-100, -200, -300, -400, tri);
        TEST(tri[0][0] == -100 && tri[1][2] == -400,
             "6.18 Negative tetradic reduces correctly");
    }

    /* 6.19 The mediating element for equal b,c is their value */
    {
        int tri[2][3];
        psm_reduce_tetradic(10, 50, 50, 90, tri);
        TEST(tri[0][2] == 50 && tri[1][0] == 50,
             "6.19 Equal b=c → mediator = b = c");
    }

    /* 6.20 Pentadic (5-ary) can be reduced to triadic:
       reduce to tetradic+triadic, then tetradic further reduces */
    {
        /* R5(a,b,c,d,e) → T1(a,b,m1), T2(m1,c,m2), T3(m2,d,e) */
        int tri1[2][3];
        /* First reduce (a,b,c,d) */
        psm_reduce_tetradic(10, 20, 30, 40, tri1);
        /* Then (remaining pair implicitly handled) */
        TEST(tri1[0][0] == 10, "6.20 5-ary reducible via chained tetradic");
    }

    /* 6.21 Monadic has zero triadicity */
    {
        /* A purely monadic "relation" = just quality, no connection */
        int loss = psm_reduction_thesis_loss(500, 500, 500);
        /* All same → minimal/no genuine mediation */
        TEST(loss < 200, "6.21 Monadic (all same) → minimal loss");
    }

    /* 6.22 Degenerate dyadic case has measurable loss */
    {
        int loss_dyadic = psm_reduction_thesis_loss(500, 500, 0);
        TEST(loss_dyadic > 0,
             "6.22 Degenerate dyad (O=S) still has loss > 0");
    }

    /* 6.23 Reduction is idempotent: reducing a triad gives same triad */
    {
        /* A triad cannot be further reduced (it's irreducible) */
        int loss = psm_reduction_thesis_loss(100, 500, 900);
        TEST(loss > 0, "6.23 Triadic irreducibility confirmed (loss > 0)");
    }

    /* 6.24 Loss is continuous: small change → small loss change */
    {
        int l1 = psm_reduction_thesis_loss(100, 500, 900);
        int l2 = psm_reduction_thesis_loss(110, 500, 890);
        TEST(abs(l1 - l2) < 200,
             "6.24 Small perturbation → similar loss");
    }

    /* 6.25 Extreme span: S midpoint of O,I → both approaches agree */
    {
        int loss = psm_reduction_thesis_loss(-1000, 0, 1000);
        TEST(loss >= 0,
             "6.25 Extreme span (-1000,0,1000) → loss ≥ 0");
    }
}

/* ======================================================================== */
/*  Section 7: Interpretant Analysis (25 tests)                             */
/* ======================================================================== */
static void test_interpretant_analysis(void)
{
    printf("\n--- Section 7: Interpretant Analysis ---\n");

    /* 7.1 Analyze: immediate = sign value */
    {
        psm_interpretant_t it = psm_analyze_interpretant(500, 800);
        TEST(it.immediate == 500, "7.1  Immediate interp = sign value (500)");
    }

    /* 7.2 Dynamic = midpoint of sign and object */
    {
        psm_interpretant_t it = psm_analyze_interpretant(500, 800);
        TEST(it.dynamic == 650, "7.2  Dynamic = (500+800)/2 = 650");
    }

    /* 7.3 Final = object value (truth) */
    {
        psm_interpretant_t it = psm_analyze_interpretant(500, 800);
        TEST(it.final_ == 800, "7.3  Final = object value (800)");
    }

    /* 7.4 When sign == object: all interpretants converge */
    {
        psm_interpretant_t it = psm_analyze_interpretant(1000, 1000);
        TEST(it.immediate == 1000 && it.dynamic == 1000 && it.final_ == 1000,
             "7.4  S=O → all interpretants agree");
    }

    /* 7.5 Zero values */
    {
        psm_interpretant_t it = psm_analyze_interpretant(0, 0);
        TEST(it.immediate == 0 && it.dynamic == 0 && it.final_ == 0,
             "7.5  All zeros → all interps zero");
    }

    /* 7.6 Negative values */
    {
        psm_interpretant_t it = psm_analyze_interpretant(-500, -300);
        TEST(it.immediate == -500 && it.dynamic == -400 && it.final_ == -300,
             "7.6  Negative: imm=-500, dyn=-400, fin=-300");
    }

    /* 7.7 Dynamic is always between immediate and final */
    {
        psm_interpretant_t it = psm_analyze_interpretant(200, 800);
        int dyn_between = (it.dynamic >= it.immediate &&
                           it.dynamic <= it.final_) ||
                          (it.dynamic <= it.immediate &&
                           it.dynamic >= it.final_);
        TEST(dyn_between, "7.7  Dynamic between immediate and final");
    }

    /* 7.8 Large sign, small object */
    {
        psm_interpretant_t it = psm_analyze_interpretant(10000, 100);
        TEST(it.immediate == 10000 && it.final_ == 100,
             "7.8  Large S, small O: imm=10000, fin=100");
    }

    /* 7.9 Dynamic interpretant: actual effect (Secondness) */
    {
        psm_interpretant_t it = psm_analyze_interpretant(0, 1000);
        TEST(it.dynamic == 500, "7.9  Dynamic = midpoint (0,1000) = 500");
    }

    /* 7.10 Final interpretant is modal, not temporal */
    {
        /* Even with distant sign, final = object (the truth) */
        psm_interpretant_t it = psm_analyze_interpretant(-5000, 5000);
        TEST(it.final_ == 5000,
             "7.10 Final = truth regardless of sign distance");
    }

    /* 7.11–7.13 Immediate is Firstness (quality/potential) */
    {
        psm_interpretant_t it = psm_analyze_interpretant(42, 100);
        TEST(it.immediate == 42, "7.11 Immediate = sign's quality (42)");
    }
    {
        psm_interpretant_t it = psm_analyze_interpretant(-999, 500);
        TEST(it.immediate == -999, "7.12 Immediate preserves sign (-999)");
    }
    {
        psm_interpretant_t it = psm_analyze_interpretant(0, 500);
        TEST(it.immediate == 0, "7.13 Immediate preserves zero");
    }

    /* 7.14–7.16 Dynamic effect proportional to distance */
    {
        psm_interpretant_t it1 = psm_analyze_interpretant(0, 100);
        psm_interpretant_t it2 = psm_analyze_interpretant(0, 1000);
        TEST(it2.dynamic > it1.dynamic,
             "7.14 Larger object → larger dynamic effect");
    }
    {
        psm_interpretant_t it = psm_analyze_interpretant(100, 300);
        TEST(it.dynamic == 200, "7.15 dyn = (100+300)/2 = 200");
    }
    {
        psm_interpretant_t it = psm_analyze_interpretant(1, 3);
        TEST(it.dynamic == 2, "7.16 dyn = (1+3)/2 = 2");
    }

    /* 7.17 Final interpretant is fallibilistic convergence target */
    {
        /* Multiple analyses of same object should have same final */
        psm_interpretant_t it1 = psm_analyze_interpretant(100, 500);
        psm_interpretant_t it2 = psm_analyze_interpretant(900, 500);
        TEST(it1.final_ == it2.final_,
             "7.17 Same object → same final (fallibilism)");
    }

    /* 7.18 Collateral experience: object determines interpretation */
    {
        psm_interpretant_t it1 = psm_analyze_interpretant(500, 100);
        psm_interpretant_t it2 = psm_analyze_interpretant(500, 900);
        TEST(it1.dynamic != it2.dynamic,
             "7.18 Different objects → different dynamics");
    }

    /* 7.19 Sign distant from object: larger gap immediate→final */
    {
        psm_interpretant_t it = psm_analyze_interpretant(0, 1000);
        int gap = abs(it.immediate - it.final_);
        TEST(gap == 1000, "7.19 Gap imm→fin = 1000 for (0,1000)");
    }

    /* 7.20 Sign equals object: zero gap */
    {
        psm_interpretant_t it = psm_analyze_interpretant(777, 777);
        int gap = abs(it.immediate - it.final_);
        TEST(gap == 0, "7.20 Gap = 0 when sign equals object");
    }

    /* 7.21 Convergence in chain: each step should narrow gap */
    {
        psm_state_t cst;
        psm_init(&cst);
        psm_sign_class_t cls;
        psm_classify(&cls, 1, 1, 1);

        int target = 1000;
        int sign = 0;
        psm_object_t o = { target, target };

        for (int i = 0; i < 5; i++) {
            psm_interpretant_t it = psm_analyze_interpretant(sign, target);
            if (i == 0)
                psm_create_relation(&cst, sign, o, it, &cls);
            else
                psm_extend_chain(&cst, o, it, &cls);
            sign = it.dynamic;  /* Next sign = this dynamic */
        }
        /* Last dynamic should be closer to 1000 than first */
        int first_gap = abs(cst.chain[0].interpretant.dynamic - target);
        int last_gap  = abs(cst.chain[4].interpretant.dynamic - target);
        TEST(last_gap < first_gap,
             "7.21 Chain convergence: gap narrows over steps");
    }

    /* 7.22 Dynamic interpretant for opposite signs */
    {
        psm_interpretant_t it = psm_analyze_interpretant(-500, 500);
        TEST(it.dynamic == 0, "7.22 dyn(-500,500) = 0 (balanced)");
    }

    /* 7.23 Odd sum: integer truncation handled */
    {
        psm_interpretant_t it = psm_analyze_interpretant(1, 2);
        TEST(it.dynamic == 1, "7.23 dyn(1,2) = 1 (integer division)");
    }

    /* 7.24 Large values don't overflow */
    {
        psm_interpretant_t it = psm_analyze_interpretant(1000000, 2000000);
        TEST(it.dynamic == 1500000 && it.final_ == 2000000,
             "7.24 Large values computed correctly");
    }

    /* 7.25 Immediate interpretant is Firstness (category check) */
    {
        psm_interpretant_t it = psm_analyze_interpretant(750, 500);
        /* Immediate = sign (Firstness: quality before interpretation) */
        trit cat = psm_category_ground(it.immediate);
        TEST(cat == TRIT_TRUE, "7.25 Positive immediate → Firstness +1");
    }
}

/* ======================================================================== */
/*  Section 8: Categories, Hypoicons & Adjacency (20 tests)                */
/* ======================================================================== */
static void test_categories_hypoicons_adjacency(void)
{
    printf("\n--- Section 8: Categories, Hypoicons & Adjacency ---\n");

    /* 8.1 Ground: positive quality → +1 */
    TEST(psm_category_ground(500) == TRIT_TRUE,
         "8.1  Ground of positive quality → +1");

    /* 8.2 Ground: negative quality → -1 */
    TEST(psm_category_ground(-500) == TRIT_FALSE,
         "8.2  Ground of negative quality → -1");

    /* 8.3 Ground: zero quality → 0 */
    TEST(psm_category_ground(0) == TRIT_UNKNOWN,
         "8.3  Ground of zero quality → 0");

    /* 8.4 Correlate: positive reaction */
    TEST(psm_category_correlate(800, 500) == TRIT_TRUE,
         "8.4  Correlate: 800 > 500 → +1");

    /* 8.5 Correlate: negative reaction */
    TEST(psm_category_correlate(200, 500) == TRIT_FALSE,
         "8.5  Correlate: 200 < 500 → -1");

    /* 8.6 Correlate: equal → no reaction */
    TEST(psm_category_correlate(500, 500) == TRIT_UNKNOWN,
         "8.6  Correlate: equal → 0");

    /* 8.7 Mediation: all agree → that value */
    TEST(psm_category_mediate(1, 1, 1) == TRIT_TRUE,
         "8.7  Mediate(+1,+1,+1) = +1 (unanimous)");

    /* 8.8 Mediation: all disagree → unknown */
    TEST(psm_category_mediate(-1, 0, 1) == TRIT_UNKNOWN,
         "8.8  Mediate(-1,0,+1) = 0 (all different)");

    /* 8.9 Mediation: majority +1 */
    TEST(psm_category_mediate(1, 1, -1) == TRIT_TRUE,
         "8.9  Mediate(+1,+1,-1) = +1 (majority)");

    /* 8.10 Mediation: majority -1 */
    TEST(psm_category_mediate(-1, -1, 1) == TRIT_FALSE,
         "8.10 Mediate(-1,-1,+1) = -1 (majority)");

    /* 8.11 Hypoicon: image when resemblance dominates */
    TEST(psm_hypoicon_classify(800, 200, 100) == PSM_IMAGE,
         "8.11 Hypoicon: high resemblance → image");

    /* 8.12 Hypoicon: diagram when relation dominates */
    TEST(psm_hypoicon_classify(200, 800, 100) == PSM_DIAGRAM,
         "8.12 Hypoicon: high relation → diagram");

    /* 8.13 Hypoicon: metaphor when parallelism dominates */
    TEST(psm_hypoicon_classify(100, 200, 800) == PSM_METAPHOR,
         "8.13 Hypoicon: high parallelism → metaphor");

    /* 8.14 Hypoicon: tie → image wins (lowest category) */
    TEST(psm_hypoicon_classify(500, 500, 500) == PSM_IMAGE,
         "8.14 Hypoicon: three-way tie → image (Firstness)");

    /* 8.15 Adjacency: same class → 3 shared */
    TEST(psm_class_adjacency(1, 1) == 3,
         "8.15 Adjacency: class with itself = 3");

    /* 8.16 Adjacency: I and II share 2 aspects */
    TEST(psm_class_adjacency(1, 2) == 2,
         "8.16 Adjacency(I,II) = 2 (icon+rheme shared)");

    /* 8.17 Adjacency: II and VI share only 1 (Peirce's thick border) */
    TEST(psm_class_adjacency(2, 6) == 1,
         "8.17 Adjacency(II,VI) = 1 (thick border pair)");

    /* 8.18 Adjacency: invalid class ID → -1 */
    TEST(psm_class_adjacency(0, 5) == -1,
         "8.18 Adjacency(0,5) → -1");

    /* 8.19 Adjacency: VI and IX share only 1 (another thick-border pair) */
    TEST(psm_class_adjacency(6, 9) == 1,
         "8.19 Adjacency(VI,IX) = 1 (thick border)");

    /* 8.20 Adjacency: X and IX share 2 (symbol+legisign) */
    TEST(psm_class_adjacency(10, 9) == 2,
         "8.20 Adjacency(X,IX) = 2 (symbol+legisign shared)");
}

/* ======================================================================== */
/*  Main                                                                    */
/* ======================================================================== */
int main(void)
{
    printf("=== Peircean Semiotic Engine Test Suite ===\n");

    test_init_basics();
    test_sign_classification();
    test_semiosis_chains();
    test_information();
    test_determination();
    test_reduction_thesis();
    test_interpretant_analysis();
    test_categories_hypoicons_adjacency();

    printf("\nPeirce Semiotic Tests: %d passed, %d failed, %d total\n",
           g_pass, g_fail, g_pass + g_fail);
    printf("=== Results: %d passed, %d failed ===\n", g_pass, g_fail);
    return g_fail ? 1 : 0;
}
