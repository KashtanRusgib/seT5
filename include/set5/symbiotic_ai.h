/*==============================================================================
 * seT5/seT6 — Symbiotic AI Module
 * include/set5/symbiotic_ai.h
 *
 * Three ternary primitives for Corner 3 AI-human partnership:
 *   trit_curiosity_probe()   — rate curiosity-value of an unknown domain
 *   trit_beauty_symmetry()   — score lattice-symmetry of a trit vector
 *   trit_eudaimonic_weight() — combine curiosity+beauty+safety into priority
 *
 * All functions are pure (no side effects) and produce values in {F,U,T}.
 * Sigma 9 compliant. Generated: 2026-02-19
 *============================================================================*/
#ifndef SET5_SYMBIOTIC_AI_H
#define SET5_SYMBIOTIC_AI_H

#include "set5/trit.h"

#ifdef __cplusplus
extern "C"
{
#endif

    /*
     * trit_curiosity_probe — Assess curiosity value of a trit domain.
     *
     * Returns:
     *   TRIT_TRUE    — domain has high exploration value (≥50% Unknown trits)
     *   TRIT_UNKNOWN — domain has moderate exploration value (any Unknown present)
     *   TRIT_FALSE   — domain fully determined (0 Unknown trits)
     *
     * @param domain  Pointer to array of trit values
     * @param len     Length of the array (must be > 0)
     */
    trit trit_curiosity_probe(const trit *domain, int len);

    /*
     * trit_beauty_symmetry — Score the lattice symmetry of a trit vector.
     *
     * A vector is "symmetric" if it is palindromic (reads same L→R and R→L).
     * Returns:
     *   TRIT_TRUE    — perfect palindrome (fully symmetric)
     *   TRIT_UNKNOWN — partial symmetry (first half matches Unknown convention)
     *   TRIT_FALSE   — no symmetry
     *
     * @param vec  Pointer to array of trit values
     * @param len  Length of the array (must be > 0)
     */
    trit trit_beauty_symmetry(const trit *vec, int len);

    /*
     * trit_eudaimonic_weight — Combine curiosity, beauty, and safety into priority.
     *
     * Priority encoding:
     *   True   + True   + True   → TRIT_TRUE    (fully eudaimonic)
     *   any False in inputs      → TRIT_FALSE   (disqualified)
     *   otherwise (any Unknown)  → TRIT_UNKNOWN (needs resolution)
     *
     * @param curiosity  Curiosity score trit
     * @param beauty     Beauty score trit
     * @param safety     Safety score trit (TRIT_FALSE = harmful, blocks scheduling)
     */
    trit trit_eudaimonic_weight(trit curiosity, trit beauty, trit safety);

#ifdef __cplusplus
}
#endif

#endif /* SET5_SYMBIOTIC_AI_H */
