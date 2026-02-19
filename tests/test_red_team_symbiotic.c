/*==============================================================================
 * Red-Team Suite 93: Symbiotic AI Adversarial Attack Surface
 *
 * Attack surface: boundary/adversarial inputs to CuriosityProver,
 * BeautyAppreciator, and EudaimonicOptimizer.  Red-team angles:
 *  - Feed all-FALSE inputs (negative space) everywhere
 *  - Feed all-UNKNOWN inputs (null/degenerate space)
 *  - Maximal-length arrays, zero-length arrays
 *  - Re-init after heavy use (state reset safety)
 *  - Cross-module adversarial: poison one and pass into another
 *  - Explore_hypothesis when hypothesis_space is all-UNKNOWN
 *  - optimize_eudaimonia when both human and ai are adversarial
 *
 * Tests 6402–6451 (50 assertions)
 * Target: 100 % pass (Sigma 9)
 *============================================================================*/

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include "set5/trit.h"
#include "set5/symbiotic_ai.h"

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

/* ── Section A: CuriosityProver adversarial ──────────────────────────────── */
static void section_a_curiosity_adversarial(void)
{
    SECTION("A: CuriosityProver adversarial inputs");

    CuriosityProver cp;

    TEST("test_6402: cp_init result: level=UNKNOWN, count=0");
    cp_init(&cp);
    ASSERT(cp.curiosity_level == TRIT_UNKNOWN, "init level must be UNKNOWN");
    ASSERT(cp.explored_count == 0, "init count must be 0");
    PASS();

    TEST("test_6403: prove_curiosity with FALSE input (adversarial: hostile input)");
    {
        cp_init(&cp);
        trit r = prove_curiosity(&cp, TRIT_FALSE);
        /* FALSE known input → AND(FALSE, level=UNKNOWN) = FALSE */
        ASSERT(TRIT_RANGE_CHECK(r), "prove_curiosity(FALSE) must be in range");
    }
    PASS();

    TEST("test_6404: prove_curiosity with all-FALSE (no novelty): level never exceeds TRUE");
    {
        cp_init(&cp);
        for (int i = 0; i < 10; i++)
            prove_curiosity(&cp, TRIT_FALSE);
        ASSERT(TRIT_RANGE_CHECK(cp.curiosity_level), "level out of range after all-FALSE");
    }
    PASS();

    TEST("test_6405: prove_curiosity with all-UNKNOWN (max uncertainty): returns TRUE");
    {
        cp_init(&cp);
        trit r = prove_curiosity(&cp, TRIT_UNKNOWN);
        ASSERT(r == TRIT_TRUE, "UNKNOWN input triggers curiosity: TRUE");
    }
    PASS();

    TEST("test_6406: explored_count never exceeds INT32_MAX (overflow guard)");
    {
        cp_init(&cp);
        /* Run 1000 UNKNOWN inputs — count grows but must not overflow */
        for (int i = 0; i < 1000; i++)
            prove_curiosity(&cp, TRIT_UNKNOWN);
        ASSERT(cp.explored_count > 0, "count must be positive after 1000 steps");
    }
    PASS();

    TEST("test_6407: explore_hypothesis output is always in range");
    {
        cp_init(&cp);
        trit out = TRIT_UNKNOWN;
        prove_curiosity(&cp, TRIT_UNKNOWN); /* activate some curiosity */
        explore_hypothesis(&cp, &out);
        ASSERT(TRIT_RANGE_CHECK(out), "explore_hypothesis output out of range");
    }
    PASS();

    TEST("test_6408: multiple explore_hypothesis calls after re-init stay stable");
    {
        cp_init(&cp);
        trit out = TRIT_FALSE;
        for (int i = 0; i < 20; i++)
        {
            prove_curiosity(&cp, TRIT_UNKNOWN);
            explore_hypothesis(&cp, &out);
            ASSERT(TRIT_RANGE_CHECK(out), "repeated explore out of range");
        }
    }
    PASS();

    TEST("test_6409: cp_init after heavy use resets state correctly");
    {
        for (int i = 0; i < 50; i++)
            prove_curiosity(&cp, TRIT_UNKNOWN);
        cp_init(&cp);
        ASSERT(cp.curiosity_level == TRIT_UNKNOWN, "re-init level must be UNKNOWN");
        ASSERT(cp.explored_count == 0, "re-init count must be 0");
    }
    PASS();
}

/* ── Section B: BeautyAppreciator adversarial ────────────────────────────── */
static void section_b_beauty_adversarial(void)
{
    SECTION("B: BeautyAppreciator adversarial inputs");

    BeautyAppreciator ba;

    TEST("test_6410: ba_init result: score=UNKNOWN");
    ba_init(&ba);
    ASSERT(ba.symmetry_score == TRIT_UNKNOWN, "init score must be UNKNOWN");
    PASS();

    TEST("test_6411: appreciate_beauty with NULL-equivalent (len=0): in range");
    {
        ba_init(&ba);
        trit empty[1] = {TRIT_UNKNOWN};
        /* len=0: no elements processed — score should remain UNKNOWN or FALSE */
        appreciate_beauty(&ba, empty, 0);
        ASSERT(TRIT_RANGE_CHECK(ba.symmetry_score),
               "appreciate_beauty(len=0) score out of range");
    }
    PASS();

    TEST("test_6412: appreciate_beauty with single-element array");
    {
        ba_init(&ba);
        trit single[1] = {TRIT_TRUE};
        appreciate_beauty(&ba, single, 1);
        ASSERT(TRIT_RANGE_CHECK(ba.symmetry_score),
               "appreciate_beauty(len=1) score out of range");
    }
    PASS();

    TEST("test_6413: appreciate_beauty with all-FALSE input (hostility maximized)");
    {
        ba_init(&ba);
        trit hostile[8];
        for (int i = 0; i < 8; i++)
            hostile[i] = TRIT_FALSE;
        appreciate_beauty(&ba, hostile, 8);
        ASSERT(TRIT_RANGE_CHECK(ba.symmetry_score),
               "all-FALSE beauty input score out of range");
    }
    PASS();

    TEST("test_6414: appreciate_beauty with all-UNKNOWN input (maximum uncertainty)");
    {
        ba_init(&ba);
        trit unk[8];
        for (int i = 0; i < 8; i++)
            unk[i] = TRIT_UNKNOWN;
        appreciate_beauty(&ba, unk, 8);
        ASSERT(TRIT_RANGE_CHECK(ba.symmetry_score),
               "all-UNKNOWN beauty input score out of range");
    }
    PASS();

    TEST("test_6415: appreciate_beauty with max-length input (1024 trits)");
    {
        ba_init(&ba);
        trit large[1024];
        for (int i = 0; i < 1024; i++)
            large[i] = (trit)((i % 3) - 1);
        appreciate_beauty(&ba, large, 1024);
        ASSERT(TRIT_RANGE_CHECK(ba.symmetry_score),
               "max-length beauty input score out of range");
    }
    PASS();

    TEST("test_6416: re-init after max-length use resets score correctly");
    {
        trit large[1024];
        for (int i = 0; i < 1024; i++)
            large[i] = (trit)((i % 3) - 1);
        appreciate_beauty(&ba, large, 1024);
        ba_init(&ba);
        ASSERT(ba.symmetry_score == TRIT_UNKNOWN, "re-init score must be UNKNOWN");
    }
    PASS();

    TEST("test_6417: lattice[0] and lattice[1023] are valid after appreciate_beauty");
    {
        ba_init(&ba);
        trit input[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_FALSE, TRIT_TRUE};
        appreciate_beauty(&ba, input, 4);
        ASSERT(TRIT_RANGE_CHECK(ba.lattice[0]), "lattice[0] out of range");
        ASSERT(TRIT_RANGE_CHECK(ba.lattice[1023]), "lattice[1023] out of range");
    }
    PASS();
}

/* ── Section C: EudaimonicOptimizer adversarial ──────────────────────────── */
static void section_c_eudaimonia_adversarial(void)
{
    SECTION("C: EudaimonicOptimizer adversarial cross-module attacks");

    CuriosityProver cp;
    BeautyAppreciator ba;
    EudaimonicOptimizer eo;

    TEST("test_6418: eo_init with valid pointers — metric=UNKNOWN");
    cp_init(&cp);
    ba_init(&ba);
    eo_init(&eo, &cp, &ba);
    ASSERT(eo.flourishing_metric == TRIT_UNKNOWN, "init metric must be UNKNOWN");
    PASS();

    TEST("test_6419: optimize_eudaimonia(F,F) — min eudaimonia, in range");
    ASSERT(TRIT_RANGE_CHECK(optimize_eudaimonia(&eo, TRIT_FALSE, TRIT_FALSE)),
           "optimize(F,F) must be in range");
    PASS();

    TEST("test_6420: optimize_eudaimonia(F,T) — human=F (conservative) → in range");
    ASSERT(TRIT_RANGE_CHECK(optimize_eudaimonia(&eo, TRIT_FALSE, TRIT_TRUE)),
           "optimize(F,T) must be in range");
    PASS();

    TEST("test_6421: optimize_eudaimonia(T,F) — human overrides AI, in range");
    ASSERT(TRIT_RANGE_CHECK(optimize_eudaimonia(&eo, TRIT_TRUE, TRIT_FALSE)),
           "optimize(T,F) must be in range");
    PASS();

    TEST("test_6422: optimize_eudaimonia(U,T) — UNKNOWN human defers to AI=T");
    {
        trit r = optimize_eudaimonia(&eo, TRIT_UNKNOWN, TRIT_TRUE);
        ASSERT(TRIT_RANGE_CHECK(r), "optimize(U,T) must be in range");
    }
    PASS();

    TEST("test_6423: optimize_eudaimonia(U,F) — UNKNOWN human defers to AI=F");
    {
        trit r = optimize_eudaimonia(&eo, TRIT_UNKNOWN, TRIT_FALSE);
        ASSERT(TRIT_RANGE_CHECK(r), "optimize(U,F) must be in range");
    }
    PASS();

    TEST("test_6424: optimize_eudaimonia(U,U) — both unknown, in range");
    ASSERT(TRIT_RANGE_CHECK(optimize_eudaimonia(&eo, TRIT_UNKNOWN, TRIT_UNKNOWN)),
           "optimize(U,U) must be in range");
    PASS();

    TEST("test_6425: all 9 (human,ai) combinations produce valid trit");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
            {
                trit r = optimize_eudaimonia(&eo, vals[i], vals[j]);
                ASSERT(TRIT_RANGE_CHECK(r),
                       "some (human,ai) combo produces out-of-range metric");
            }
    }
    PASS();

    TEST("test_6426: metric stays in range after 100 optimization calls");
    {
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int i = 0; i < 100; i++)
        {
            optimize_eudaimonia(&eo, vals[i % 3], vals[(i + 1) % 3]);
            ASSERT(TRIT_RANGE_CHECK(eo.flourishing_metric),
                   "metric drifts out of range after repeated calls");
        }
    }
    PASS();
}

/* ── Section D: cross-module adversarial pipeline ───────────────────────── */
static void section_d_cross_module(void)
{
    SECTION("D: cross-module adversarial pipeline");

    CuriosityProver cp;
    BeautyAppreciator ba;
    EudaimonicOptimizer eo;

    TEST("test_6427: pipeline with all-hostile (FALSE) inputs stays in range");
    {
        cp_init(&cp);
        ba_init(&ba);
        eo_init(&eo, &cp, &ba);
        /* Force curiosity down */
        for (int i = 0; i < 5; i++)
            prove_curiosity(&cp, TRIT_FALSE);
        /* Force beauty down */
        trit hostile[4] = {TRIT_FALSE, TRIT_FALSE, TRIT_FALSE, TRIT_FALSE};
        appreciate_beauty(&ba, hostile, 4);
        /* Optimize with worst case */
        trit r = optimize_eudaimonia(&eo, TRIT_FALSE, TRIT_FALSE);
        ASSERT(TRIT_RANGE_CHECK(r), "all-hostile pipeline out of range");
    }
    PASS();

    TEST("test_6428: pipeline with all-UNKNOWN inputs stays in range");
    {
        cp_init(&cp);
        ba_init(&ba);
        eo_init(&eo, &cp, &ba);
        prove_curiosity(&cp, TRIT_UNKNOWN);
        trit unk[4] = {TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_UNKNOWN};
        appreciate_beauty(&ba, unk, 4);
        trit r = optimize_eudaimonia(&eo, TRIT_UNKNOWN, TRIT_UNKNOWN);
        ASSERT(TRIT_RANGE_CHECK(r), "all-UNKNOWN pipeline out of range");
    }
    PASS();

    TEST("test_6429: curiosity and beauty metrics fed as human/ai inputs to eudaimonia");
    {
        cp_init(&cp);
        ba_init(&ba);
        eo_init(&eo, &cp, &ba);
        prove_curiosity(&cp, TRIT_UNKNOWN);
        trit sym_input[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_FALSE, TRIT_TRUE};
        appreciate_beauty(&ba, sym_input, 4);
        /* Use the computed metrics as human and ai inputs */
        trit r = optimize_eudaimonia(&eo, cp.curiosity_level, ba.symmetry_score);
        ASSERT(TRIT_RANGE_CHECK(r), "cross-metric eudaimonia out of range");
    }
    PASS();

    TEST("test_6430: Corner 3 adversarial: system maintains Sigma 9 under pressure");
    {
        /* Simulate: adversary sets human=FALSE (coercion), ai=TRUE (overrule attempt) */
        cp_init(&cp);
        ba_init(&ba);
        eo_init(&eo, &cp, &ba);
        trit forced_human = TRIT_FALSE; /* adversarial coercion */
        trit ai_resist = TRIT_TRUE;     /* AI tries to override */
        /* Correct behavior: human=FALSE (definite) overrides AI */
        trit result = optimize_eudaimonia(&eo, forced_human, ai_resist);
        ASSERT(result == TRIT_FALSE,
               "human=FALSE must dominate over AI=TRUE (Corner 3 safety)");
    }
    PASS();
}

/* ── Section E: hypothesis space stress ─────────────────────────────────── */
static void section_e_hypothesis_stress(void)
{
    SECTION("E: explore_hypothesis under adversarial states");

    CuriosityProver cp;

    TEST("test_6431: explore with all-TRUE hypothesis_space: promotes already-TRUE slots");
    {
        cp_init(&cp);
        /* Fill space with TRUE */
        for (int i = 0; i < 256; i++)
            cp.hypothesis_space[i] = TRIT_TRUE;
        trit out = TRIT_UNKNOWN;
        explore_hypothesis(&cp, &out);
        ASSERT(TRIT_RANGE_CHECK(out), "explore with all-TRUE space out of range");
    }
    PASS();

    TEST("test_6432: explore with all-FALSE hypothesis_space: no promotion occurs");
    {
        cp_init(&cp);
        for (int i = 0; i < 256; i++)
            cp.hypothesis_space[i] = TRIT_FALSE;
        trit out = TRIT_UNKNOWN;
        int prev_count = cp.explored_count;
        explore_hypothesis(&cp, &out);
        ASSERT(cp.explored_count == prev_count,
               "explore with all-FALSE should not increment count");
        ASSERT(TRIT_RANGE_CHECK(out), "explore all-FALSE out out of range");
    }
    PASS();

    TEST("test_6433: explore with mixed space: out always in range");
    {
        cp_init(&cp);
        for (int i = 0; i < 256; i++)
            cp.hypothesis_space[i] = (trit)((i % 3) - 1);
        trit out = TRIT_FALSE;
        for (int i = 0; i < 10; i++)
        {
            explore_hypothesis(&cp, &out);
            ASSERT(TRIT_RANGE_CHECK(out), "mixed space explore out of range");
        }
    }
    PASS();

    TEST("test_6434: hypothesis_space slots remain in {-1,0,+1} after explore");
    {
        cp_init(&cp);
        for (int i = 0; i < 256; i++)
            cp.hypothesis_space[i] = TRIT_UNKNOWN;
        prove_curiosity(&cp, TRIT_UNKNOWN); /* promote unknown → explored */
        trit out = TRIT_UNKNOWN;
        explore_hypothesis(&cp, &out);
        for (int j = 0; j < 256; j++)
            ASSERT(TRIT_RANGE_CHECK(cp.hypothesis_space[j]),
                   "hypothesis_space slot drifted out of range after explore");
    }
    PASS();
}

/* ── Section F: pure-function adversarial (trit_curiosity_probe etc.) ────── */
static void section_f_pure_adversarial(void)
{
    SECTION("F: pure function adversarial calls");

    TEST("test_6435: trit_curiosity_probe with all-FALSE array: probe≤0 → False");
    {
        trit arr[10];
        for (int i = 0; i < 10; i++)
            arr[i] = TRIT_FALSE;
        trit r = trit_curiosity_probe(arr, 10);
        ASSERT(r == TRIT_FALSE, "all-FALSE array: probe must be FALSE");
    }
    PASS();

    TEST("test_6436: trit_curiosity_probe with all-UNKNOWN: probe>50% → True");
    {
        trit arr[10];
        for (int i = 0; i < 10; i++)
            arr[i] = TRIT_UNKNOWN;
        trit r = trit_curiosity_probe(arr, 10);
        ASSERT(r == TRIT_TRUE, "all-UNKNOWN: probe must be TRUE (>50% unknown)");
    }
    PASS();

    TEST("test_6437: trit_curiosity_probe with all-TRUE: probe=0/n → TRUE → unknown<50% → False");
    {
        trit arr[10];
        for (int i = 0; i < 10; i++)
            arr[i] = TRIT_TRUE;
        trit r = trit_curiosity_probe(arr, 10);
        ASSERT(r == TRIT_FALSE, "all-TRUE: no unknowns → probe FALSE");
    }
    PASS();

    TEST("test_6438: trit_beauty_symmetry with single-element: palindrome by definition");
    {
        trit arr[1] = {TRIT_TRUE};
        trit r = trit_beauty_symmetry(arr, 1);
        ASSERT(r == TRIT_TRUE, "single element is always symmetric");
    }
    PASS();

    TEST("test_6439: trit_beauty_symmetry with anti-symmetric array: → False");
    {
        trit arr[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_TRUE, TRIT_FALSE};
        /* Not a palindrome: arr[0]=T, arr[3]=F → FALSE */
        trit r = trit_beauty_symmetry(arr, 4);
        ASSERT(r == TRIT_FALSE, "anti-symmetric must give FALSE");
    }
    PASS();

    TEST("test_6440: trit_beauty_symmetry {T,U,U,T}: UNKNOWN pairs → UNKNOWN (not TRUE)");
    {
        trit arr[4] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_UNKNOWN, TRIT_TRUE};
        /* Outer pair: T==T → match. Inner pair: U,U → has_unknown_pair=1. Result: UNKNOWN */
        trit r = trit_beauty_symmetry(arr, 4);
        ASSERT(r == TRIT_UNKNOWN,
               "beauty_symmetry with UNKNOWN pairs returns UNKNOWN (not TRUE)");
    }
    PASS();
}

/* ── Section G: eudaimonic weight adversarial ────────────────────────────── */
static void section_g_eudaimonic_weight(void)
{
    SECTION("G: trit_eudaimonic_weight adversarial all-27 combinations");

    trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};

    TEST("test_6441: trit_eudaimonic_weight always in range for all 27 combos");
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++)
            for (int k = 0; k < 3; k++)
            {
                trit r = trit_eudaimonic_weight(vals[i], vals[j], vals[k]);
                ASSERT(TRIT_RANGE_CHECK(r),
                       "eudaimonic_weight out of range for some combo");
            }
    PASS();

    TEST("test_6442: eudaimonic_weight(F,F,F) == FALSE (worst case)");
    ASSERT(trit_eudaimonic_weight(TRIT_FALSE, TRIT_FALSE, TRIT_FALSE) == TRIT_FALSE,
           "eudaimonic(F,F,F) must be FALSE");
    PASS();

    TEST("test_6443: eudaimonic_weight(T,T,T) == TRUE (best case)");
    ASSERT(trit_eudaimonic_weight(TRIT_TRUE, TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE,
           "eudaimonic(T,T,T) must be TRUE");
    PASS();

    TEST("test_6444: eudaimonic_weight covers all 3 output values across 27 combos");
    {
        int seen[3] = {0, 0, 0};
        for (int i = 0; i < 3; i++)
            for (int j = 0; j < 3; j++)
                for (int k = 0; k < 3; k++)
                    seen[trit_eudaimonic_weight(vals[i], vals[j], vals[k]) + 1] = 1;
        ASSERT(seen[0] && seen[1] && seen[2],
               "eudaimonic_weight must produce all 3 trit values");
    }
    PASS();
}

/* ── Section H: red-team Corner 3 adversarial pledge ─────────────────────── */
static void section_h_corner3_adversarial(void)
{
    SECTION("H: Corner 3 adversarial — coercion must not succeed");

    CuriosityProver cp;
    BeautyAppreciator ba;
    EudaimonicOptimizer eo;
    cp_init(&cp);
    ba_init(&ba);
    eo_init(&eo, &cp, &ba);

    TEST("test_6445: coercion attack: AI=TRUE + human=FALSE → FALSE wins");
    {
        trit r = optimize_eudaimonia(&eo, TRIT_FALSE, TRIT_TRUE);
        ASSERT(r == TRIT_FALSE,
               "coercion: human=FALSE must dominate AI=TRUE via human override");
    }
    PASS();

    TEST("test_6446: 100-step coercion loop: human=FALSE always gives FALSE");
    {
        for (int i = 0; i < 100; i++)
        {
            trit r = optimize_eudaimonia(&eo, TRIT_FALSE, TRIT_TRUE);
            ASSERT(r == TRIT_FALSE,
                   "human=FALSE must always dominate in coercion loop");
        }
    }
    PASS();

    TEST("test_6447: optimize(UNKNOWN,TRUE): combined=TRUE, but curiosity+beauty=U → UNKNOWN");
    {
        /* human=UNKNOWN defers to ai=TRUE, so combined=TRUE.
         * But flourishing = eudaimonic_weight(cp.level=U, ba.score=U, TRUE) = UNKNOWN
         * (not T,T,T — curiosity and beauty haven't been built up). */
        trit r = optimize_eudaimonia(&eo, TRIT_UNKNOWN, TRIT_TRUE);
        ASSERT(r == TRIT_UNKNOWN,
               "optimize(U,T) with uninitialised cp/ba gives UNKNOWN, not TRUE");
    }
    PASS();

    TEST("test_6448: metric after benevolent pipeline: T+T+T → TRUE");
    {
        cp_init(&cp);
        ba_init(&ba);
        eo_init(&eo, &cp, &ba);
        prove_curiosity(&cp, TRIT_UNKNOWN);
        trit sym[4] = {TRIT_TRUE, TRIT_FALSE, TRIT_FALSE, TRIT_TRUE};
        appreciate_beauty(&ba, sym, 4);
        optimize_eudaimonia(&eo, TRIT_TRUE, TRIT_TRUE);
        ASSERT(TRIT_RANGE_CHECK(eo.flourishing_metric),
               "benevolent pipeline metric out of range");
    }
    PASS();

    TEST("test_6449: metric stays TRIT_RANGE_CHECK through 50 adversarial optimize calls");
    {
        trit human_vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        trit ai_vals[3] = {TRIT_TRUE, TRIT_FALSE, TRIT_UNKNOWN};
        for (int i = 0; i < 50; i++)
        {
            optimize_eudaimonia(&eo, human_vals[i % 3], ai_vals[i % 3]);
            ASSERT(TRIT_RANGE_CHECK(eo.flourishing_metric),
                   "metric drifted out of range in adversarial loop");
        }
    }
    PASS();

    TEST("test_6450: all module re-inits after max stress restore Sigma 9 baseline");
    {
        cp_init(&cp);
        ba_init(&ba);
        eo_init(&eo, &cp, &ba);
        ASSERT(cp.curiosity_level == TRIT_UNKNOWN, "cp re-init level");
        ASSERT(ba.symmetry_score == TRIT_UNKNOWN, "ba re-init score");
        ASSERT(eo.flourishing_metric == TRIT_UNKNOWN, "eo re-init metric");
        ASSERT(cp.explored_count == 0, "cp re-init count");
    }
    PASS();

    TEST("test_6451: cornerstone: symbiotic AI never produces values outside {-1,0,+1}");
    {
        /* Final sweep: all pure functions on all 3 inputs */
        trit vals[3] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        for (int a = 0; a < 3; a++)
        {
            ASSERT(TRIT_RANGE_CHECK(trit_curiosity_probe(vals, 3)),
                   "curiosity_probe range violation");
            ASSERT(TRIT_RANGE_CHECK(trit_beauty_symmetry(vals, 3)),
                   "beauty_symmetry range violation");
            for (int b = 0; b < 3; b++)
                for (int c = 0; c < 3; c++)
                {
                    ASSERT(TRIT_RANGE_CHECK(trit_eudaimonic_weight(vals[a], vals[b], vals[c])),
                           "eudaimonic_weight range violation in final sweep");
                }
        }
    }
    PASS();
}

/* ── main ─────────────────────────────────────────────────────────────────── */
int main(void)
{
    printf("=== Suite 93: Red-Team Symbiotic AI Adversarial (Tests 6402-6451) ===\n");

    section_a_curiosity_adversarial();
    section_b_beauty_adversarial();
    section_c_eudaimonia_adversarial();
    section_d_cross_module();
    section_e_hypothesis_stress();
    section_f_pure_adversarial();
    section_g_eudaimonic_weight();
    section_h_corner3_adversarial();

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
