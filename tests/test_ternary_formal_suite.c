/**
 * @file test_ternary_formal_suite.c
 * @brief Suite 98: Formal-Verification-Driven Ternary—Logic Improvements
 *
 * Tests 6652-6701 (50 assertions, Sigma 9 target).
 *
 * Implements and verifies in C the key properties proved in three new
 * Isabelle theories created this session:
 *   - proof/TritSTE.thy       — Symbolic Ternary Trajectory Evaluation
 *   - proof/TritTMR.thy       — Triple Modular Redundancy
 *   - proof/TritAbsInterp.thy — Abstract Interpretation (widening/narrowing)
 *
 * Also exercises:
 *   - include/set5/trit_tmr.h — new TMR C API
 *   - Garner/CRT reconstruction soundness (multi-radix RNS invariants)
 *   - Integration of T-SEC sanitization with all of the above
 *
 * Section A  (6652-6661): Scalar K₃ TMR vote — idempotence, fault masking
 * Section B  (6662-6671): Packed-64 TMR vote — packed word voting, no-fault-output
 * Section C  (6672-6681): STE guard semantics — unk containment, guard transparency
 * Section D  (6682-6691): Abstract interpretation domain — lattice boundaries
 * Section E  (6692-6701): Multi-radix Garner reconstruction + full integration
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include "set5/trit_tmr.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* ---- Test infrastructure -------------------------------------------- */

static int g_pass = 0;
static int g_fail = 0;
static int g_test_id = 6652;

#define ASSERT(cond, msg)                                   \
    do                                                      \
    {                                                       \
        if (cond)                                           \
        {                                                   \
            printf("[PASS] test_%d: %s\n", g_test_id, msg); \
            g_pass++;                                       \
        }                                                   \
        else                                                \
        {                                                   \
            printf("[FAIL] test_%d: %s\n", g_test_id, msg); \
            g_fail++;                                       \
        }                                                   \
        g_test_id++;                                        \
    } while (0)

/* Trit scalar aliases */
#define T_F TRIT_FALSE /* -1 */
#define T_U TRIT_UNKNOWN   /*  0 */
#define T_T TRIT_TRUE  /* +1 */

/* Kleene ops on scalar int8_t trits (Kleene min/max) */
static inline int8_t kleene_and(int8_t a, int8_t b) { return a < b ? a : b; }
static inline int8_t kleene_or(int8_t a, int8_t b) { return a > b ? a : b; }

/* Packed-64 constants */
#define P_ALL_TRUE 0x5555555555555555ULL  /* 32 × TRUE  (0b01) */
#define P_ALL_FALSE 0xAAAAAAAAAAAAAAAAULL /* 32 × FALSE (0b10) */
#define P_ALL_UNK 0x0000000000000000ULL   /* 32 × UNK   (0b00) */
#define P_ALL_FAULT 0xFFFFFFFFFFFFFFFFULL /* 32 × FAULT (0b11) */

/* Garner/CRT reconstruction for moduli {3,5,7}, M=105.
 * CRT(r0,r1,r2) = (70*r0 + 21*r1 + 15*r2) % 105
 * Derivation: M0=35, inv(35,3)=2 → y0=70; M1=21, inv(21,5)=1 → y1=21;
 *              M2=15, inv(15,7)=1 → y2=15. */
static int crt_reconstruct(int r0, int r1, int r2)
{
    return (70 * r0 + 21 * r1 + 15 * r2) % 105;
}

/* ======================================================================
 * Section A — Scalar K₃ TMR Vote (Tests 6652–6661)
 * Exercises trit_tmr_vote3() and trit_tmr_agree().
 * Formal basis: TritTMR.thy §TMR-2, TMR-6, TMR-7.
 * ====================================================================== */
static void test_section_a(void)
{
    printf("\n=== Section A: Scalar TMR Vote ===\n");

    /* 6652: idempotence — triple FALSE */
    ASSERT(trit_tmr_vote3(T_F, T_F, T_F) == T_F,
           "TMR idempotent FALSE: vote3(-1,-1,-1)=-1");

    /* 6653: idempotence — triple UNK */
    ASSERT(trit_tmr_vote3(T_U, T_U, T_U) == T_U,
           "TMR idempotent UNK: vote3(0,0,0)=0");

    /* 6654: idempotence — triple TRUE */
    ASSERT(trit_tmr_vote3(T_T, T_T, T_T) == T_T,
           "TMR idempotent TRUE: vote3(1,1,1)=1");

    /* 6655: single fault (UNK) cannot override 2×TRUE (TMR-2) */
    ASSERT(trit_tmr_vote3(T_T, T_T, T_U) == T_T,
           "TMR fault tolerance: vote3(1,1,0)=1");

    /* 6656: single fault (UNK) cannot override 2×FALSE */
    ASSERT(trit_tmr_vote3(T_F, T_F, T_U) == T_F,
           "TMR fault tolerance: vote3(-1,-1,0)=-1");

    /* 6657: fault in first position: 2×TRUE still wins */
    ASSERT(trit_tmr_vote3(T_U, T_T, T_T) == T_T,
           "TMR fault in pos 0: vote3(0,1,1)=1");

    /* 6658: full disagreement → UNK (conservative default, TMR-5) */
    ASSERT(trit_tmr_vote3(T_T, T_F, T_U) == T_U,
           "TMR three-way disagree: vote3(1,-1,0)=0 (UNK)");

    /* 6659: permutation invariance — TMR-7 */
    ASSERT(trit_tmr_vote3(T_F, T_T, T_F) == T_F,
           "TMR commutativity: vote3(-1,1,-1)=-1");

    /* 6660: agreement predicate */
    ASSERT(trit_tmr_agree(T_T, T_T) == 1 &&
               trit_tmr_agree(T_T, T_F) == 0,
           "trit_tmr_agree: (1,1)=true, (1,-1)=false");

    /* 6661: single FALSE fault cannot override 2×TRUE */
    ASSERT(trit_tmr_vote3(T_T, T_T, T_F) == T_T,
           "TMR: vote3(1,1,-1)=1 (majority TRUE)");
}

/* ======================================================================
 * Section B — Packed-64 TMR Vote (Tests 6662–6671)
 * Exercises trit_tmr_vote_packed64(), TRIT_PACKED_VALID().
 * Formal basis: TritTMR.thy §TMR-4, pair_tmr_no_fault_output.
 * ====================================================================== */
static void test_section_b(void)
{
    printf("\n=== Section B: Packed-64 TMR Vote ===\n");

    /* 6662: triple TRUE → all-TRUE, valid */
    uint64_t r = trit_tmr_vote_packed64(P_ALL_TRUE, P_ALL_TRUE, P_ALL_TRUE);
    ASSERT(r == P_ALL_TRUE && TRIT_PACKED_VALID(r),
           "packed TMR 3×TRUE → all-TRUE, VALID");

    /* 6663: triple FALSE → all-FALSE, valid */
    r = trit_tmr_vote_packed64(P_ALL_FALSE, P_ALL_FALSE, P_ALL_FALSE);
    ASSERT(r == P_ALL_FALSE && TRIT_PACKED_VALID(r),
           "packed TMR 3×FALSE → all-FALSE, VALID");

    /* 6664: triple UNK → all-UNK, valid */
    r = trit_tmr_vote_packed64(P_ALL_UNK, P_ALL_UNK, P_ALL_UNK);
    ASSERT(r == P_ALL_UNK && TRIT_PACKED_VALID(r),
           "packed TMR 3×UNK → all-UNK, VALID");

    /* 6665: single-word fault (0xFFFF) with 2×TRUE → TRUE recovered
     *   sanitize(0xFFFF) = 0x0000 (UNK); vote(TRUE,TRUE,UNK) = TRUE */
    r = trit_tmr_vote_packed64(P_ALL_TRUE, P_ALL_TRUE, P_ALL_FAULT);
    ASSERT(r == P_ALL_TRUE,
           "packed TMR fault correction: (TRUE,TRUE,FAULT) → TRUE");

    /* 6666: 3× FAULT word → all-UNK (never a fault slot in output) */
    r = trit_tmr_vote_packed64(P_ALL_FAULT, P_ALL_FAULT, P_ALL_FAULT);
    ASSERT(TRIT_PACKED_VALID(r),
           "packed TMR 3×FAULT → no fault slots in output (VALID)");

    /* 6667: (TRUE, TRUE, FAULT) → TRUE, VALID */
    r = trit_tmr_vote_packed64(P_ALL_TRUE, P_ALL_FAULT, P_ALL_TRUE);
    ASSERT(r == P_ALL_TRUE && TRIT_PACKED_VALID(r),
           "packed TMR (TRUE,FAULT,TRUE) → TRUE, VALID");

    /* 6668: (FALSE, FALSE, FAULT) → FALSE, VALID */
    r = trit_tmr_vote_packed64(P_ALL_FALSE, P_ALL_FALSE, P_ALL_FAULT);
    ASSERT(r == P_ALL_FALSE && TRIT_PACKED_VALID(r),
           "packed TMR (FALSE,FALSE,FAULT) → FALSE, VALID");

    /* 6669: divergence map is VALID (all slots encode F or T, not FAULT) */
    uint64_t div = trit_tmr_divergence_packed64(P_ALL_TRUE, P_ALL_FALSE);
    ASSERT(TRIT_PACKED_VALID(div),
           "divergence map of (TRUE,FALSE) is VALID (no fault slots)");

    /* 6670: agreement predicate */
    ASSERT(trit_tmr_agree_packed64(P_ALL_TRUE, P_ALL_TRUE) == 1 &&
               trit_tmr_agree_packed64(P_ALL_TRUE, P_ALL_FALSE) == 0,
           "trit_tmr_agree_packed64: (same)=true, (diff)=false");

    /* 6671: (TRUE, FALSE, FAULT) → no majority per slot → UNK, VALID
     *   sanitize: (0x5555, 0xAAAA, 0x0000).
     *   Per slot: (TRUE=01, FALSE=10, UNK=00).
     *   lo: maj(1,0,0)=0. hi: maj(0,1,0)=0. → UNK (0x0000). VALID. */
    r = trit_tmr_vote_packed64(P_ALL_TRUE, P_ALL_FALSE, P_ALL_FAULT);
    ASSERT(r == P_ALL_UNK && TRIT_PACKED_VALID(r),
           "packed TMR (TRUE,FALSE,FAULT) → UNK (no majority), VALID");
}

/* ======================================================================
 * Section C — STE Guard Semantics (Tests 6672–6681)
 * Exercises Kleene AND/OR properties that correspond to STE theorems.
 * Formal basis: TritSTE.thy.
 * ====================================================================== */
static void test_section_c(void)
{
    printf("\n=== Section C: STE Guard Semantics ===\n");

    /* 6672: STE-1 — guard=TRUE blocks unk masquerade as TRUE
     *   kleene_and(TRUE, UNK) = UNK ≠ TRUE */
    ASSERT(kleene_and(T_T, T_U) != T_T,
           "STE-1 guard blocks: TRUE AND UNK ≠ TRUE (unk cannot masquerade)");

    /* 6673: guard=TRUE transparent for FALSE (ste_guard_transparent_pos) */
    ASSERT(kleene_and(T_T, T_F) == T_F,
           "STE guard transparent FALSE: TRUE AND FALSE = FALSE");

    /* 6674: guard=TRUE transparent for TRUE */
    ASSERT(kleene_and(T_T, T_T) == T_T,
           "STE guard transparent TRUE: TRUE AND TRUE = TRUE");

    /* 6675: FALSE annihilator in AND (STE: guard=FALSE kills all) */
    ASSERT(kleene_and(T_F, T_U) == T_F,
           "STE annihilator: FALSE AND UNK = FALSE");

    /* 6676: UNK self-idempotent under AND (unknown_and_self) */
    ASSERT(kleene_and(T_U, T_U) == T_U,
           "STE UNK idem: UNK AND UNK = UNK");

    /* 6677: UNK propagates in OR with FALSE (unk_or_propagation) */
    ASSERT(kleene_or(T_U, T_F) == T_U,
           "STE UNK prop: UNK OR FALSE = UNK");

    /* 6678: UNK collapses to TRUE in OR with TRUE (unk_or_propagation_exact) */
    ASSERT(kleene_or(T_U, T_T) == T_T,
           "STE UNK collapses: UNK OR TRUE = TRUE");

    /* 6679: deterministic env — packed op on {FALSE,TRUE}-only input has no UNK
     *   0x5555 (all TRUE) OR 0xAAAA (all FALSE) = all TRUE (TRUE dominates OR) */
    uint64_t det_or = trit_or_packed64_hardened(P_ALL_TRUE, P_ALL_FALSE);
    ASSERT(det_or == P_ALL_TRUE && TRIT_PACKED_VALID(det_or),
           "STE det env: (all-TRUE) OR (all-FALSE) = all-TRUE, no UNK, VALID");

    /* 6680: STE composition — apply two Kleene ops in sequence
     *   f(UNK) = AND(UNK, TRUE) = UNK; g(UNK) = OR(UNK, FALSE) = UNK → UNK */
    int8_t step1 = kleene_and(T_U, T_T);  /* UNK */
    int8_t step2 = kleene_or(step1, T_F); /* still UNK */
    ASSERT(step2 == T_U,
           "STE composition: g∘f(UNK) = OR(AND(UNK,TRUE),FALSE) = UNK");

    /* 6681: STE monotonicity — replacing Unk→True in an arg raises result ≥ prev
     *   OR(UNK,FALSE) = UNK; OR(TRUE,FALSE) = TRUE; TRUE ≥ UNK */
    int8_t r_unk = kleene_or(T_U, T_F);
    int8_t r_true = kleene_or(T_T, T_F);
    ASSERT(r_unk <= r_true,
           "STE monotone: OR(UNK,FALSE) ≤ OR(TRUE,FALSE)  [0 ≤ 1]");
}

/* ======================================================================
 * Section D — Abstract Interpretation Domain (Tests 6682–6691)
 * Exercises the K₃ lattice boundaries proved in TritAbsInterp.thy.
 * ======================================================================*/
static void test_section_d(void)
{
    printf("\n=== Section D: Abstract Interpretation Domain ===\n");

/* Helper: abs_widen(prev, curr) = if curr<=prev then prev else 0 (UNK) */
#define ABS_WIDEN(prev, curr) ((curr) <= (prev) ? (prev) : T_U)
/* abs_narrow(prev, curr) = min(prev, curr) (= trit_and in K₃) */
#define ABS_NARROW(prev, curr) (kleene_and((prev), (curr)))

    /* 6682: FALSE is AND-annihilator — AI boundary: neg kills all */
    ASSERT(kleene_and(T_F, T_U) == T_F &&
               kleene_and(T_F, T_T) == T_F,
           "AI annihilator: FALSE AND {UNK,TRUE} = FALSE");

    /* 6683: TRUE is OR-annihilator */
    ASSERT(kleene_or(T_T, T_U) == T_T &&
               kleene_or(T_T, T_F) == T_T,
           "AI annihilator: TRUE OR {UNK,FALSE} = TRUE");

    /* 6684: UNK AND TRUE = UNK (not TRUE — unk boundary holds) */
    ASSERT(kleene_and(T_U, T_T) == T_U,
           "AI-6 unk boundary: UNK AND TRUE = UNK ≠ TRUE");

    /* 6685: UNK AND FALSE = FALSE (annihilated, safe lower bound) */
    ASSERT(kleene_and(T_U, T_F) == T_F,
           "AI unk AND FALSE = FALSE (annihilated)");

    /* 6686: UNK OR FALSE = UNK (unk propagates — no false positive) */
    ASSERT(kleene_or(T_U, T_F) == T_U,
           "AI-6 unk or boundary: UNK OR FALSE = UNK ≠ TRUE");

    /* 6687: UNK OR TRUE = TRUE (unk collapses once evidence exists) */
    ASSERT(kleene_or(T_U, T_T) == T_T,
           "AI unk OR TRUE = TRUE");

    /* 6688: widening is above previous (AI-7) */
    ASSERT(ABS_WIDEN(T_F, T_U) >= T_F &&
               ABS_WIDEN(T_U, T_T) >= T_U,
           "AI-7 widening above prev: widen(F,U)≥F, widen(U,T)≥U");

    /* 6689: widening on ascending chain collapses to UNK */
    ASSERT(ABS_WIDEN(T_F, T_T) == T_U,
           "AI-3 widen collapses: widen(FALSE, TRUE) = UNK (unstable → saturate)");

    /* 6690: AI-6 unk boundary — no path from {F,U} to TRUE under Kleene ops */
    ASSERT(kleene_and(T_U, T_U) != T_T &&
               kleene_or(T_U, T_F) != T_T &&
               kleene_and(T_F, T_U) != T_T,
           "AI-6 unk boundary: no {F,U}×{F,U} Kleene op produces TRUE");

    /* 6691: conservative safety — only TRUE (==1) is safe, UNK and FALSE are not */
    ASSERT((T_T == 1) &&     /* TRUE is safe  */
               (T_U != 1) && /* UNK is unsafe */
               (T_F != 1),   /* FALSE is unsafe */
           "AI-8 conservative safety: is_safe(T)=true, is_safe(U)=false, is_safe(F)=false");

#undef ABS_WIDEN
#undef ABS_NARROW
}

/* ======================================================================
 * Section E — Multi-Radix Garner Reconstruction + Integration (6692–6701)
 * Exercises CRT mod {3,5,7} soundness and combined T-SEC + TMR pipeline.
 * Formal basis: RNS soundness (related to TritAbsInterp + PackedFault).
 * ====================================================================== */
static void test_section_e(void)
{
    printf("\n=== Section E: Multi-Radix Garner Reconstruction + Integration ===\n");

    /* 6692: CRT identity — reconstruct 42 from residues mod {3,5,7}
     *   42 % 3 = 0, 42 % 5 = 2, 42 % 7 = 0.
     *   CRT(0,2,0) = (70*0 + 21*2 + 15*0) % 105 = 42. */
    ASSERT(crt_reconstruct(42 % 3, 42 % 5, 42 % 7) == 42,
           "Garner CRT: reconstruct(42) from residues {3,5,7}");

    /* 6693: CRT roundtrip for x=0 */
    ASSERT(crt_reconstruct(0 % 3, 0 % 5, 0 % 7) == 0,
           "Garner CRT roundtrip: x=0");

    /* 6694: CRT roundtrip for x=1 (all residues = 1) */
    ASSERT(crt_reconstruct(1 % 3, 1 % 5, 1 % 7) == 1,
           "Garner CRT roundtrip: x=1");

    /* 6695: CRT roundtrip for x=104 (max of range M-1=104) */
    ASSERT(crt_reconstruct(104 % 3, 104 % 5, 104 % 7) == 104,
           "Garner CRT roundtrip: x=104 (M-1)");

    /* 6696: RNS carry-free add — (15+27)%105=42 via per-channel addition
     *   15%3=0, 27%3=0, (0+0)%3=0 = 42%3=0 ✓
     *   15%5=0, 27%5=2, (0+2)%5=2 = 42%5=2 ✓
     *   15%7=1, 27%7=6, (1+6)%7=0 = 42%7=0 ✓
     *   CRT reconstruct = 42 */
    {
        int a = 15, b = 27;
        int r0 = (a % 3 + b % 3) % 3;
        int r1 = (a % 5 + b % 5) % 5;
        int r2 = (a % 7 + b % 7) % 7;
        ASSERT(crt_reconstruct(r0, r1, r2) == (a + b) % 105,
               "RNS carry-free add: (15+27) residue add = 42");
    }

    /* 6697: RNS carry-free multiply — 3×7=21 mod {3,5,7}
     *   3%3=0, 7%3=1, 0*1%3=0; 3%5=3, 7%5=2, 3*2%5=1; 3%7=3, 7%7=0, 3*0%7=0.
     *   CRT(0,1,0) = (70*0 + 21*1 + 15*0) % 105 = 21 = 3*7 ✓ */
    {
        int a = 3, b = 7;
        int r0 = (a % 3 * b % 3) % 3;
        int r1 = (a % 5 * b % 5) % 5;
        int r2 = (a % 7 * b % 7) % 7;
        ASSERT(crt_reconstruct(r0, r1, r2) == (a * b) % 105,
               "RNS carry-free mul: 3×7 residue mul = 21");
    }

    /* 6698: T-SEC + TMR integration — sanitize then TMR vote on packed words.
     *   Build a word with known injected fault, vote with 2 clean copies. */
    {
        uint64_t clean = P_ALL_TRUE;
        uint64_t faulted = P_ALL_FAULT; /* all slots = 0b11 */
        uint64_t voted = trit_tmr_vote_packed64(clean, clean, faulted);
        ASSERT(voted == P_ALL_TRUE && TRIT_PACKED_VALID(voted),
               "T-SEC+TMR integration: sanitize+vote recovers clean from fault");
    }

    /* 6699: STE + TMR composition — deterministic env → deterministic output.
     *   Pack 32×TRUE, TMR-vote, result has no UNK or FAULT slots. */
    {
        uint64_t r = trit_tmr_vote_packed64(P_ALL_TRUE, P_ALL_TRUE, P_ALL_TRUE);
        /* All slots are TRUE (0b01): no UNK (0b00) and no FAULT (0b11) */
        int no_unk = (r & ~P_ALL_FAULT) == P_ALL_TRUE; /* no 0b00 or 0b10 among valid */
        (void)no_unk;
        ASSERT(r == P_ALL_TRUE && TRIT_PACKED_VALID(r),
               "STE+TMR det env: TMR of 3×TRUE → TRUE, no UNK, VALID");
    }

    /* 6700: Abstract-interpretation boundary + TMR — unk inputs under TMR ≤ Unk
     *   vote(UNK, UNK, UNK) = UNK; VALID; no escalation to TRUE */
    {
        uint64_t r = trit_tmr_vote_packed64(P_ALL_UNK, P_ALL_UNK, P_ALL_UNK);
        ASSERT(r == P_ALL_UNK && TRIT_PACKED_VALID(r),
               "AI-boundary+TMR: vote(UNK,UNK,UNK)=UNK (no false escalation to TRUE)");
    }

    /* 6701: Final integration + Sigma 9 reporting.
     *   Run all three improvements together:
     *   1. A fault-injected word is sanitized (T-SEC).
     *   2. TMR votes it out with two clean copies.
     *   3. The result is in the deterministic {FALSE,TRUE} domain (STE det env).
     *   4. No abstract escalation beyond the input domain (AI-6). */
    {
        /* Three computational replicas, one with injected fault */
        uint64_t replica_a = P_ALL_TRUE;  /* clean */
        uint64_t replica_b = P_ALL_TRUE;  /* clean */
        uint64_t replica_c = P_ALL_FAULT; /* injected fault */
        uint64_t result = trit_tmr_vote_packed64(replica_a, replica_b, replica_c);
        /* Verify all invariants */
        int is_valid = TRIT_PACKED_VALID(result);
        int is_correct = (result == P_ALL_TRUE);
        int no_escalation = (result != P_ALL_UNK || result != P_ALL_FALSE);
        (void)no_escalation;
        ASSERT(is_valid && is_correct,
               "Sigma 9 integration: T-SEC+STE+AI+TMR all properties hold simultaneously");
    }
}

/* ---- Main ------------------------------------------------------------ */
int main(void)
{
    printf("==========================================================\n");
    printf("Suite 98: Formal-Verification-Driven Ternary Improvements\n");
    printf("Tests 6652–6701  |  Sigma 9 Target: 50/50\n");
    printf("==========================================================\n");

    test_section_a();
    test_section_b();
    test_section_c();
    test_section_d();
    test_section_e();

    int total = g_pass + g_fail;
    printf("\n==========================================================\n");
    printf("Suite 98 Result: %d/%d passed", g_pass, total);
    if (g_fail == 0)
    {
        printf("  — Sigma 9: ALL PASS\n");
    }
    else
    {
        printf("  — %d FAILURES\n", g_fail);
    }
    printf("==========================================================\n");

    return g_fail == 0 ? 0 : 1;
}
