/**
 * @file trit_tekum_float.c
 * @brief seT6 Tekum Arithmetic — Implementation
 *
 * Balanced ternary tapered precision floats (Hunhold, arXiv:2512.10964v1).
 * All arithmetic integer-only, ×1000 fixed-point.
 *
 * Key property: rounding = truncation in balanced ternary.
 * Max truncation error < 0.5 ulp (proven in Cook/Parhami, confirmed here).
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "trit_tekum_float.h"
#include <string.h>

/* ==== Helpers =========================================================== */

/** Integer power of 3 (3^exp), clamped to prevent overflow */
static int64_t pow3(int exp) {
    if (exp < 0) return 0;
    if (exp > 19) return (int64_t)1162261467;  /* cap at 3^19 */
    int64_t r = 1;
    for (int i = 0; i < exp; i++) r *= 3;
    return r;
}

/** Integer log base 3 (floor) */
static int log3(int64_t v) {
    if (v <= 0) return 0;
    int r = 0;
    while (v >= 3) { v /= 3; r++; }
    return r;
}

/** Integer log base 2 (floor) */
static int log2i(int64_t v) {
    if (v <= 0) return 0;
    int r = 0;
    while (v >= 2) { v /= 2; r++; }
    return r;
}

/** Exponent bias: b(r) = sign(r) * floor((3^max(0,|r|-2) + 1) / 2) */
static int tekum_bias(int r) {
    static const int lookup[] = { 0, 1, 2, 4, 10, 28, 82, 244 };
    int ar = (r < 0) ? -r : r;
    if (ar > 7) ar = 7;
    int b = lookup[ar];
    return (r < 0) ? -b : (r > 0) ? b : 0;
}

/** Exponent trit count: c(r) = max(0, |r| - 2) */
static int tekum_expo_trits(int r) {
    int ar = (r < 0) ? -r : r;
    int c = ar - 2;
    return (c > 0) ? c : 0;
}

/** Convert balanced ternary trit array to integer */
static int trits_to_int(const int8_t *trits, int n) {
    int val = 0, pw = 1;
    for (int i = 0; i < n; i++) {
        val += trits[i] * pw;
        pw *= 3;
    }
    return val;
}

/** Convert integer to balanced ternary trit array */
static void int_to_trits(int val, int8_t *trits, int n) {
    int neg = 0;
    if (val < 0) { neg = 1; val = -val; }
    for (int i = 0; i < n; i++) {
        int rem = val % 3;
        val /= 3;
        if (rem == 0)      trits[i] = 0;
        else if (rem == 1)  trits[i] = neg ? -1 : 1;
        else {              trits[i] = neg ? 1 : -1; val++; }
    }
}

/** Check if all trits are the same value */
static int all_trits_equal(const int8_t *trits, int n, int8_t val) {
    for (int i = 0; i < n; i++)
        if (trits[i] != val) return 0;
    return 1;
}

/** Compute the anchor: anc(t) = |t| - 1T...1T (the midpoint subtraction) */
static void compute_anchor(const int8_t *trits, int n, int8_t *anchor) {
    /* |t| */
    int8_t abs_t[TEKUM_MAX_TRITS];
    int val = trits_to_int(trits, n);
    if (val < 0) val = -val;
    int_to_trits(val, abs_t, n);

    /* 1T...1T pattern (midpoint for even n) */
    int8_t mid[TEKUM_MAX_TRITS];
    for (int i = 0; i < n; i++)
        mid[i] = (i % 2 == 0) ? -1 : 1;  /* low to high: T,1,T,1,... */

    /* Subtract: anchor = abs(t) - midpoint */
    int a_int = trits_to_int(abs_t, n);
    int m_int = trits_to_int(mid, n);
    int_to_trits(a_int - m_int, anchor, n);
}

/* ==== Public API ======================================================== */

int tekum_init(tekum_state_t *st, int width) {
    if (!st) return -1;
    if (width < TEKUM_MIN_TRITS || (width % 2) != 0) return -1;
    if (width > TEKUM_MAX_TRITS) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    st->default_width = width;
    st->trunc_is_round = 1;  /* fundamental property */
    return 0;
}

int tekum_encode(tekum_state_t *st, int val_x1000, tekum_word_t *out) {
    if (!st || !st->initialized || !out) return -1;
    memset(out, 0, sizeof(*out));
    out->n = st->default_width;

    /* Special cases */
    if (val_x1000 == TEKUM_NAR) {
        for (int i = 0; i < out->n; i++) out->trits[i] = -1;
        return 0;
    }
    if (val_x1000 == TEKUM_INF) {
        for (int i = 0; i < out->n; i++) out->trits[i] = 1;
        return 0;
    }
    if (val_x1000 == 0) {
        /* All zeros */
        return 0;
    }

    st->ops_performed++;

    /* Determine sign */
    int sign = (val_x1000 > 0) ? 1 : -1;
    int64_t abs_val = (val_x1000 > 0) ? val_x1000 : -val_x1000;

    /* Find exponent: value = (1 + f) * 3^e * 1000
     * So 3^e ≈ abs_val / 1000 when f is small */
    int e = 0;
    if (abs_val >= 1000) {
        int64_t v = abs_val / 1000;
        e = log3(v);
        /* Refine: if 3^(e+1) is closer */
        int64_t p3e = pow3(e);
        int64_t p3e1 = pow3(e + 1);
        if (p3e1 > 0 && abs_val >= (int64_t)(p3e + p3e1) * 500)
            e++;
    } else if (abs_val > 0) {
        /* Value < 1.0: need negative exponent */
        int64_t v = 1000;
        while (v > abs_val * 3 && e > -180) {
            v /= 3;
            e--;
            if (v == 0) break;
        }
    }

    /* Compute fraction: f = val / 3^e - 1, in ×1000 */
    int64_t p3e = pow3(e >= 0 ? e : 0);
    int frac_x1000;
    if (e >= 0 && p3e > 0) {
        frac_x1000 = (int)(abs_val / p3e) - 1000;
    } else if (e < 0) {
        int64_t scale = pow3(-e);
        frac_x1000 = (int)((abs_val * scale) / 1000) - 1000;
    } else {
        frac_x1000 = 0;
    }
    if (frac_x1000 < -499) frac_x1000 = -499;
    if (frac_x1000 > 499) frac_x1000 = 499;

    /* Find regime that maps to this exponent */
    int regime = 0;
    for (int r = -7; r <= 7; r++) {
        int c = tekum_expo_trits(r);
        int b = tekum_bias(r);
        int e_min = b - (int)((pow3(c) - 1) / 2);
        int e_max = b + (int)((pow3(c) - 1) / 2);
        if (e >= e_min && e <= e_max) {
            regime = r;
            break;
        }
    }

    int c = tekum_expo_trits(regime);
    int p = out->n - c - TEKUM_REGIME_TRITS;
    if (p < 0) p = 0;

    /* Build anchor trits: regime(3) + exponent(c) + fraction(p) */
    int8_t anchor[TEKUM_MAX_TRITS];
    memset(anchor, 0, sizeof(anchor));

    /* Fraction trits (low end) */
    int frac_int = (frac_x1000 * (int)(pow3(p))) / 1000;
    int_to_trits(frac_int, anchor, p);

    /* Exponent trits (middle) */
    int e_local = e - tekum_bias(regime);
    int8_t e_trits[TEKUM_MAX_TRITS];
    memset(e_trits, 0, sizeof(e_trits));
    int_to_trits(e_local, e_trits, c);
    for (int i = 0; i < c; i++)
        anchor[p + i] = e_trits[i];

    /* Regime trits (high end) */
    int8_t r_trits[3];
    int_to_trits(regime, r_trits, 3);
    for (int i = 0; i < 3; i++)
        anchor[p + c + i] = r_trits[i];

    /* Convert anchor back to tekum word: t = sign * (anchor + 1T...1T) */
    int8_t mid[TEKUM_MAX_TRITS];
    for (int i = 0; i < out->n; i++)
        mid[i] = (i % 2 == 0) ? -1 : 1;

    int anc_int = trits_to_int(anchor, out->n);
    int mid_int = trits_to_int(mid, out->n);
    int t_int = anc_int + mid_int;
    if (sign < 0) t_int = -t_int;

    int_to_trits(t_int, out->trits, out->n);
    return 0;
}

int tekum_decode(tekum_state_t *st, const tekum_word_t *word,
                 tekum_decoded_t *out) {
    if (!st || !st->initialized || !word || !out) return -1;
    memset(out, 0, sizeof(*out));
    out->n_trits = word->n;

    /* Check special cases */
    if (all_trits_equal(word->trits, word->n, -1)) {
        out->is_nar = 1;
        out->value_x1000 = TEKUM_NAR;
        return 0;
    }
    if (all_trits_equal(word->trits, word->n, 1)) {
        out->is_inf = 1;
        out->value_x1000 = TEKUM_INF;
        return 0;
    }
    if (all_trits_equal(word->trits, word->n, 0)) {
        out->is_zero = 1;
        out->value_x1000 = 0;
        return 0;
    }

    /* Determine sign from MSB non-zero trit */
    int val = trits_to_int(word->trits, word->n);
    out->sign = (val > 0) ? 1 : -1;

    /* Compute anchor */
    int8_t anchor[TEKUM_MAX_TRITS];
    compute_anchor(word->trits, word->n, anchor);

    /* Extract regime (top 3 trits of anchor) */
    int c_trits = tekum_expo_trits(0);  /* start assumption */
    int p_trits = word->n - c_trits - TEKUM_REGIME_TRITS;

    int8_t r_trits[3];
    for (int i = 0; i < 3; i++)
        r_trits[i] = anchor[p_trits + c_trits + i];

    out->regime = trits_to_int(r_trits, 3);
    if (out->regime < -7) out->regime = -7;
    if (out->regime > 7) out->regime = 7;

    /* Recompute with actual regime */
    int c = tekum_expo_trits(out->regime);
    int p = word->n - c - TEKUM_REGIME_TRITS;
    if (p < 0) p = 0;

    /* Extract exponent */
    int8_t e_trits[TEKUM_MAX_TRITS];
    memset(e_trits, 0, sizeof(e_trits));
    for (int i = 0; i < c && (p + i) < word->n; i++)
        e_trits[i] = anchor[p + i];
    out->exponent = trits_to_int(e_trits, c) + tekum_bias(out->regime);

    /* Extract fraction */
    int frac_int = trits_to_int(anchor, p);
    int64_t p3p = pow3(p);
    out->fraction_x1000 = (p3p > 0) ? (int)((int64_t)frac_int * 1000 / p3p) : 0;

    /* Compute value: sign * (1 + f) * 3^e */
    int64_t p3e = pow3(out->exponent >= 0 ? out->exponent : 0);
    if (out->exponent >= 0) {
        out->value_x1000 = (int)(out->sign *
            ((1000 + out->fraction_x1000) * p3e / 1000) * 1000);
        /* Simplified for large exponents */
        if (out->exponent > 12)
            out->value_x1000 = out->sign * TEKUM_INF;
    } else {
        int64_t div = pow3(-out->exponent);
        if (div > 0)
            out->value_x1000 = (int)(out->sign *
                (1000 + out->fraction_x1000) * 1000 / div / 1000);
        else
            out->value_x1000 = 0;
    }

    return 0;
}

int tekum_negate(const tekum_word_t *word, tekum_word_t *out) {
    if (!word || !out) return -1;
    out->n = word->n;
    /* Balanced ternary negation: trit-wise flip */
    for (int i = 0; i < word->n; i++)
        out->trits[i] = -word->trits[i];
    return 0;
}

int tekum_add(tekum_state_t *st, const tekum_word_t *a,
              const tekum_word_t *b, tekum_word_t *out) {
    if (!st || !st->initialized || !a || !b || !out) return -1;

    st->ops_performed++;

    /* Decode both, add values, re-encode */
    tekum_decoded_t da, db;
    tekum_decode(st, a, &da);
    tekum_decode(st, b, &db);

    /* NaR propagation */
    if (da.is_nar || db.is_nar) {
        st->nar_produced++;
        return tekum_encode(st, TEKUM_NAR, out);
    }

    int result = da.value_x1000 + db.value_x1000;

    /* Overflow check */
    if (result > TEKUM_INF / 2 || result < -TEKUM_INF / 2) {
        st->overflows++;
        return tekum_encode(st, (result > 0) ? TEKUM_INF : -TEKUM_INF, out);
    }

    return tekum_encode(st, result, out);
}

int tekum_mul(tekum_state_t *st, const tekum_word_t *a,
              const tekum_word_t *b, tekum_word_t *out) {
    if (!st || !st->initialized || !a || !b || !out) return -1;

    st->ops_performed++;

    tekum_decoded_t da, db;
    tekum_decode(st, a, &da);
    tekum_decode(st, b, &db);

    if (da.is_nar || db.is_nar) {
        st->nar_produced++;
        return tekum_encode(st, TEKUM_NAR, out);
    }

    /* Multiply: for fixed-point, (a*b) / scale */
    int64_t prod = (int64_t)da.value_x1000 * db.value_x1000 / 1000;
    if (prod > TEKUM_INF / 2) {
        st->overflows++;
        return tekum_encode(st, TEKUM_INF, out);
    }
    if (prod < -TEKUM_INF / 2) {
        st->overflows++;
        return tekum_encode(st, -TEKUM_INF, out);
    }

    return tekum_encode(st, (int)prod, out);
}

int tekum_truncate(const tekum_word_t *word, int n_trits, tekum_word_t *out) {
    if (!word || !out) return -1;
    if (n_trits < TEKUM_MIN_TRITS || (n_trits % 2) != 0) return -1;
    if (n_trits >= word->n) return -1;

    memset(out, 0, sizeof(*out));
    out->n = n_trits;

    /* Truncation in balanced ternary: simply drop the least-significant trits.
     * This IS rounding — the key insight from Cook/Hunhold/Parhami.
     * Max error < 0.5 ulp because balanced ternary fractions range (-0.5, 0.5). */
    int offset = word->n - n_trits;
    for (int i = 0; i < n_trits; i++)
        out->trits[i] = word->trits[i + offset];

    return 0;
}

int tekum_truncation_error(tekum_state_t *st,
                           const tekum_word_t *original,
                           const tekum_word_t *truncated) {
    if (!st || !original || !truncated) return -1;

    /* Balanced ternary truncation error = value of the dropped trits.
     * The dropped trits are original->trits[0..offset-1] (LSB portion).
     * Error in ulp×1000 = |Σ t_i × 3^i| / 3^offset × 1000
     * Since t_i ∈ {-1,0,+1}, max = (3^offset - 1)/(2 × 3^offset) < 0.5 */
    int offset = original->n - truncated->n;
    if (offset <= 0) return 0;

    int error = 0;
    int pw = 1;
    for (int i = 0; i < offset; i++) {
        error += original->trits[i] * pw;
        pw *= 3;
    }
    if (error < 0) error = -error;

    /* ulp = 3^offset = pw */
    if (pw <= 0) return 0;
    return (int)(((long long)error * 1000) / (long long)pw);
}

int tekum_compare(const tekum_word_t *a, const tekum_word_t *b) {
    if (!a || !b) return 0;

    /* Monotonicity: integer ordering of trit strings = tekum ordering
     * (Proposition 3 in Hunhold) */
    int va = trits_to_int(a->trits, a->n);
    int vb = trits_to_int(b->trits, b->n);

    if (va < vb) return -1;
    if (va > vb) return 1;
    return 0;
}

int tekum_radix_economy(int n) {
    if (n <= 1) return 1000;

    int log2_n = log2i((int64_t)n);
    int log3_n = log3((int64_t)n);

    int bin_economy = log2_n * 2;
    int tern_economy = log3_n * 3;

    if (bin_economy == 0) return 1000;
    return (tern_economy * 1000) / bin_economy;
}
