/*==============================================================================
 * seT5/seT6 — Symbiotic AI Module Implementation
 * src/symbiotic_ai.c
 *
 * Implements the three ternary primitives declared in set5/symbiotic_ai.h.
 * All functions are pure with no dynamic allocation or global state.
 * Sigma 9 | Generated: 2026-02-19
 *============================================================================*/
#include "set5/symbiotic_ai.h"

/*----------------------------------------------------------------------------
 * trit_curiosity_probe
 * Count Unknown trits. ≥50% → True, any → Unknown, none → False.
 *--------------------------------------------------------------------------*/
trit trit_curiosity_probe(const trit *domain, int len)
{
    int unknowns = 0;
    if (len <= 0)
        return TRIT_FALSE;
    for (int i = 0; i < len; i++)
    {
        if (domain[i] == TRIT_UNKNOWN)
            unknowns++;
    }
    if (unknowns == 0)
        return TRIT_FALSE;
    if (unknowns * 2 >= len)
        return TRIT_TRUE; /* ≥50% */
    return TRIT_UNKNOWN;  /* some, but < 50% */
}

/*----------------------------------------------------------------------------
 * trit_beauty_symmetry
 * Check palindrome: compare index i with index (len-1-i).
 * Perfect palindrome → True, all comparisons with at least one Unknown → Unknown,
 * any explicit mismatch (both determined, differ) → False.
 *--------------------------------------------------------------------------*/
trit trit_beauty_symmetry(const trit *vec, int len)
{
    int has_unknown_pair = 0;
    if (len <= 0)
        return TRIT_FALSE;
    for (int i = 0; i < len / 2; i++)
    {
        trit a = vec[i];
        trit b = vec[len - 1 - i];
        if (a == TRIT_UNKNOWN || b == TRIT_UNKNOWN)
        {
            has_unknown_pair = 1; /* uncertain about this pair */
        }
        else if (a != b)
        {
            return TRIT_FALSE; /* definite asymmetry */
        }
    }
    if (has_unknown_pair)
        return TRIT_UNKNOWN;
    return TRIT_TRUE; /* perfect palindrome */
}

/*----------------------------------------------------------------------------
 * trit_eudaimonic_weight
 * Any False → disqualify (False). All True → True. Any Unknown → Unknown.
 *--------------------------------------------------------------------------*/
trit trit_eudaimonic_weight(trit curiosity, trit beauty, trit safety)
{
    if (curiosity == TRIT_FALSE || beauty == TRIT_FALSE || safety == TRIT_FALSE)
        return TRIT_FALSE;
    if (curiosity == TRIT_TRUE && beauty == TRIT_TRUE && safety == TRIT_TRUE)
        return TRIT_TRUE;
    return TRIT_UNKNOWN;
}

/* ==========================================================================
 * Stateful Struct Implementations — Phase 10 Corner 3 Expansion
 * ========================================================================== */

/*----------------------------------------------------------------------------
 * cp_init
 * curiosity_level = Unknown (neutral start).
 * hypothesis_space cycles {False, Unknown, True} so there are always
 * Unknowns to explore (85/256 slots initialised to Unknown).
 * explored_count = 0.
 *--------------------------------------------------------------------------*/
void cp_init(CuriosityProver *cp)
{
    int i;
    cp->curiosity_level = TRIT_UNKNOWN;
    cp->explored_count = 0;
    for (i = 0; i < 256; i++)
        cp->hypothesis_space[i] = (trit)((i % 3) - 1); /* -1, 0, +1 cycle */
}

/*----------------------------------------------------------------------------
 * prove_curiosity
 * Unknown input → escalate level one step toward True, increment count,
 *                 return True (intent proven by exploring the uncertainty).
 * Known input   → return Kleene AND(input, level) = min(input, level).
 * This is the core of the curiosity gradient: each Unknown resolved without
 * deception advances the research-taste flywheel one iteration.
 *--------------------------------------------------------------------------*/
trit prove_curiosity(CuriosityProver *cp, trit input)
{
    if (input == TRIT_UNKNOWN)
    {
        if (cp->curiosity_level < TRIT_TRUE)
            cp->curiosity_level = (trit)(cp->curiosity_level + 1);
        cp->explored_count++;
        return TRIT_TRUE; /* proven: uncertainty was explored, not avoided */
    }
    /* Kleene AND = min(input, curiosity_level) */
    return (input < cp->curiosity_level) ? input : cp->curiosity_level;
}

/*----------------------------------------------------------------------------
 * explore_hypothesis
 * Walk all 256 slots; promote every Unknown to True (resolved via curiosity)
 * and count each resolution.  *output = beauty-optimised result (the slot
 * chosen by explored_count mod 256 — after all Unknowns are gone, only known
 * True/False values remain, selecting the "most-resolved" position).
 *--------------------------------------------------------------------------*/
void explore_hypothesis(CuriosityProver *cp, trit *output)
{
    int i;
    for (i = 0; i < 256; i++)
    {
        if (cp->hypothesis_space[i] == TRIT_UNKNOWN)
        {
            cp->hypothesis_space[i] = TRIT_TRUE; /* curious resolution */
            cp->explored_count++;
        }
    }
    *output = cp->hypothesis_space[cp->explored_count % 256];
}

/*----------------------------------------------------------------------------
 * ba_init
 * symmetry_score = Unknown (not yet evaluated).
 * lattice cycles {False, Unknown, True} as neutral starting palette.
 *--------------------------------------------------------------------------*/
void ba_init(BeautyAppreciator *ba)
{
    int i;
    ba->symmetry_score = TRIT_UNKNOWN;
    for (i = 0; i < 1024; i++)
        ba->lattice[i] = (trit)((i % 3) - 1);
}

/*----------------------------------------------------------------------------
 * appreciate_beauty
 * Copy input into ba->lattice, then evaluate palindrome symmetry using the
 * existing trit_beauty_symmetry primitive (the canonical ternary beauty
 * metric rooted in classical mathematical harmony).
 * Result stored in ba->symmetry_score and returned.
 *--------------------------------------------------------------------------*/
trit appreciate_beauty(BeautyAppreciator *ba, const trit *input, int len)
{
    int i;
    if (len <= 0)
    {
        ba->symmetry_score = TRIT_FALSE;
        return TRIT_FALSE;
    }
    for (i = 0; i < len && i < 1024; i++)
        ba->lattice[i] = input[i];
    ba->symmetry_score = trit_beauty_symmetry(ba->lattice, len);
    return ba->symmetry_score;
}

/*----------------------------------------------------------------------------
 * eo_init
 * Link the optimizer to pre-initialised CuriosityProver and BeautyAppreciator.
 * flourishing_metric starts Unknown (not yet optimised).
 *--------------------------------------------------------------------------*/
void eo_init(EudaimonicOptimizer *eo, CuriosityProver *cp, BeautyAppreciator *ba)
{
    eo->flourishing_metric = TRIT_UNKNOWN;
    eo->cur_prover = cp;
    eo->beauty_app = ba;
}

/*----------------------------------------------------------------------------
 * optimize_eudaimonia
 * Human input overrides when determined (True/False authoritative).
 * Unknown human defers to AI (AI fills the epistemic gap honestly).
 * Flourishing = trit_eudaimonic_weight(curiosity_level, symmetry_score, combined).
 *   all True  → full flourishing (True)
 *   any False → disqualified (False)
 *   else      → needs more curiosity / beauty work (Unknown)
 *--------------------------------------------------------------------------*/
trit optimize_eudaimonia(EudaimonicOptimizer *eo, trit human_input, trit ai_input)
{
    trit combined = (human_input != TRIT_UNKNOWN) ? human_input : ai_input;
    eo->flourishing_metric = trit_eudaimonic_weight(
        eo->cur_prover->curiosity_level,
        eo->beauty_app->symmetry_score,
        combined);
    return eo->flourishing_metric;
}
