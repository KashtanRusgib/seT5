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
