/**
 * @file  trit_peirce_semiotic.h
 * @brief seT6 – Peircean Semiotic Engine (Triadic Sign Theory)
 *
 * Implements Charles Sanders Peirce's semiotic theory as a ternary computing
 * module. Peirce's framework is fundamentally triadic: every sign relation
 * involves exactly three elements (Sign, Object, Interpretant) linked by an
 * irreducible triadic relation. This maps naturally onto balanced ternary:
 *
 *   Firstness  = -1  (quality, possibility, monadic)
 *   Secondness =  0  (reaction, actuality, dyadic)
 *   Thirdness  = +1  (representation, law, triadic)
 *
 * Three trichotomies classify every sign along three parameters:
 *   I.   Sign itself:      Qualisign(-1) / Sinsign(0) / Legisign(+1)
 *   II.  Sign→Object:      Icon(-1)      / Index(0)   / Symbol(+1)
 *   III. Sign→Interpretant: Rheme(-1)    / Dicisign(0) / Argument(+1)
 *
 * The constraint a ≥ b ≥ c yields exactly 10 valid classes (C(5,3)=10),
 * matching Peirce's Ten Classes of Sign (CP 2.254–263, MS 540, 1903).
 *
 * Additionally models:
 *   - Semiosis chains (interpretant becomes next sign)
 *   - Information = Extension × Intension (CP 2.407–8, 1867)
 *   - Immediate / Dynamic / Final interpretants
 *   - Immediate / Dynamic objects
 *   - Reduction Thesis (triads necessary, tetrads reducible)
 *   - Hypoicon classification (image / diagram / metaphor)
 *   - K3 logic integration for ternary sign operations
 *
 * References:
 *   - Peirce, C.S. (1903) "A Syllabus of Certain Topics of Logic", EP 2
 *   - Peirce, C.S. (1867) "On a New List of Categories"
 *   - Peirce, C.S. (1906) "Prolegomena to an Apology for Pragmaticism"
 *   - Peirce, C.S. (1908) "A Letter to Lady Welby", Semiotic and Significs
 *
 * All numeric values are ×1000 fixed-point (integer-only, no floats).
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET6_TRIT_PEIRCE_SEMIOTIC_H
#define SET6_TRIT_PEIRCE_SEMIOTIC_H

#include "set5/trit.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==== Constants ========================================================= */

#define PSM_FP_SCALE         1000   /**< Fixed-point scale ×1000             */
#define PSM_MAX_CHAIN        64     /**< Maximum semiosis chain length       */
#define PSM_NUM_VALID_CLASSES 10    /**< Peirce's 10 valid sign classes      */
#define PSM_NUM_TRICHOTOMIES  3     /**< I, II, III trichotomy count         */
#define PSM_MAX_SIGNS        128    /**< Maximum signs in a semiosis state   */

/** Peirce's cenopythagorean categories as trit values */
#define PSM_FIRSTNESS    ((trit)-1)  /**< Quality, possibility, monadic     */
#define PSM_SECONDNESS   ((trit) 0)  /**< Reaction, actuality, dyadic       */
#define PSM_THIRDNESS    ((trit)+1)  /**< Representation, law, triadic      */

/** Trichotomy I – sign itself */
#define PSM_QUALISIGN    PSM_FIRSTNESS   /**< Quality of feeling            */
#define PSM_SINSIGN      PSM_SECONDNESS  /**< Actual individual thing       */
#define PSM_LEGISIGN     PSM_THIRDNESS   /**< Norm, habit, rule, law        */

/** Trichotomy II – sign→object relation */
#define PSM_ICON         PSM_FIRSTNESS   /**< Resemblance/similarity        */
#define PSM_INDEX        PSM_SECONDNESS  /**< Factual/causal connection     */
#define PSM_SYMBOL       PSM_THIRDNESS   /**< Interpretive habit/convention */

/** Trichotomy III – sign→interpretant relation */
#define PSM_RHEME        PSM_FIRSTNESS   /**< Term-like, quality            */
#define PSM_DICISIGN     PSM_SECONDNESS  /**< Proposition-like, fact        */
#define PSM_ARGUMENT     PSM_THIRDNESS   /**< Argument, habit/law           */

/** Named sign class IDs (I–X, Peirce MS 540) */
#define PSM_CLASS_I      1    /**< Rhematic Iconic Qualisign               */
#define PSM_CLASS_II     2    /**< Rhematic Iconic Sinsign                 */
#define PSM_CLASS_III    3    /**< Rhematic Indexical Sinsign              */
#define PSM_CLASS_IV     4    /**< Dicent Indexical Sinsign                */
#define PSM_CLASS_V      5    /**< Rhematic Iconic Legisign                */
#define PSM_CLASS_VI     6    /**< Rhematic Indexical Legisign             */
#define PSM_CLASS_VII    7    /**< Dicent Indexical Legisign               */
#define PSM_CLASS_VIII   8    /**< Rhematic Symbol Legisign                */
#define PSM_CLASS_IX     9    /**< Dicent Symbol Legisign                  */
#define PSM_CLASS_X      10   /**< Argument Symbol Legisign                */

/** Hypoicon sub-types */
#define PSM_IMAGE        1    /**< Depends on simple quality               */
#define PSM_DIAGRAM      2    /**< Internal relations by analogy           */
#define PSM_METAPHOR     3    /**< Parallelism in something else           */

/* ==== Structures ======================================================== */

/**
 * @brief Sign classification via three trichotomies.
 *
 * Each field is a trit encoding the phenomenological category:
 *   -1 = Firstness, 0 = Secondness, +1 = Thirdness.
 * Valid classes require: sign_itself >= sign_object >= sign_interpretant.
 */
typedef struct {
    trit sign_itself;       /**< I:   qualisign/sinsign/legisign           */
    trit sign_object;       /**< II:  icon/index/symbol                    */
    trit sign_interpretant; /**< III: rheme/dicisign/argument              */
} psm_sign_class_t;

/**
 * @brief Object representation (immediate vs dynamic).
 *
 * Immediate object = object as represented in the sign.
 * Dynamic object   = object as it really is ("founded as on bedrock").
 */
typedef struct {
    int immediate;          /**< Object as represented (×1000)             */
    int dynamic;            /**< Object as it really is (×1000)            */
} psm_object_t;

/**
 * @brief Interpretant representation (immediate/dynamic/final).
 *
 * Immediate = potential meaning (Firstness, quality of impression).
 * Dynamic   = actual effect on mind (Secondness, actuality).
 * Final     = ideal effect under full inquiry (Thirdness, norm).
 */
typedef struct {
    int immediate;          /**< Potential meaning, quality (×1000)        */
    int dynamic;            /**< Actual effect on mind (×1000)             */
    int final_;             /**< Ideal/normative effect (×1000)            */
} psm_interpretant_t;

/**
 * @brief A single triadic sign relation.
 *
 * Represents the irreducible triad: Sign–Object–Interpretant.
 * The object determines the sign, which determines the interpretant.
 */
typedef struct {
    int                sign_value;   /**< Sign representation (×1000)      */
    psm_object_t       object;       /**< Object (immediate + dynamic)     */
    psm_interpretant_t interpretant; /**< Interpretant (imm/dyn/final)     */
    psm_sign_class_t   classification;  /**< Sign's trichotomy class       */
    int                class_id;     /**< Peirce class ID (I–X), 0 if unset*/
} psm_sign_relation_t;

/**
 * @brief Semiosis engine state.
 *
 * Tracks a chain of sign relations where each interpretant becomes the next
 * sign, modeling Peirce's concept of unlimited semiosis.
 */
typedef struct {
    psm_sign_relation_t chain[PSM_MAX_CHAIN];  /**< Semiosis chain        */
    int                 chain_len;              /**< Current chain length  */
    int                 total_information;      /**< Ext × Int (×1000)    */
    int                 initialized;            /**< 1 if init'd, 0 else  */
} psm_state_t;

/* ---- Inline implementations ---- */
/**
 * @file  trit_peirce_semiotic.c
 * @brief seT6 – Peircean Semiotic Engine implementation.
 *
 * Implements Peirce's triadic sign theory using balanced ternary arithmetic.
 * See trit_peirce_semiotic.h for full documentation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */


/* ==== Helpers =========================================================== */

/** Clamp integer to trit range [-1, +1]. */
static inline trit clamp_trit(int v)
{
    if (v < -1) return (trit)-1;
    if (v >  1) return (trit)+1;
    return (trit)v;
}

/** Absolute value (integer). */
static inline int iabs(int v) { return v < 0 ? -v : v; }

/** Min of two ints. */
static inline int imin(int a, int b) { return a < b ? a : b; }

/** Clamp to avoid overflow in ×1000 products. */
static inline int safe_mul_1000(int a, int b)
{
    /* a and b are ×1000. Product in real terms = (a/1000)*(b/1000)*1000
       = a*b/1000. Guard against overflow. */
    long long prod = (long long)a * (long long)b;
    long long result = prod / 1000;
    if (result > 2000000000LL) return 2000000000;
    if (result < -2000000000LL) return -2000000000;
    return (int)result;
}

/* ==== The 10 Valid Sign Classes (sorted by class ID) ==================== */

static const psm_sign_class_t g_valid_classes[10] = {
    /* I:   (-1,-1,-1) Rhematic Iconic Qualisign      */
    { PSM_QUALISIGN, PSM_ICON,   PSM_RHEME    },
    /* II:  ( 0,-1,-1) Rhematic Iconic Sinsign         */
    { PSM_SINSIGN,   PSM_ICON,   PSM_RHEME    },
    /* III: ( 0, 0,-1) Rhematic Indexical Sinsign       */
    { PSM_SINSIGN,   PSM_INDEX,  PSM_RHEME    },
    /* IV:  ( 0, 0, 0) Dicent Indexical Sinsign         */
    { PSM_SINSIGN,   PSM_INDEX,  PSM_DICISIGN },
    /* V:   (+1,-1,-1) Rhematic Iconic Legisign         */
    { PSM_LEGISIGN,  PSM_ICON,   PSM_RHEME    },
    /* VI:  (+1, 0,-1) Rhematic Indexical Legisign      */
    { PSM_LEGISIGN,  PSM_INDEX,  PSM_RHEME    },
    /* VII: (+1, 0, 0) Dicent Indexical Legisign        */
    { PSM_LEGISIGN,  PSM_INDEX,  PSM_DICISIGN },
    /* VIII:(+1,+1,-1) Rhematic Symbol Legisign         */
    { PSM_LEGISIGN,  PSM_SYMBOL, PSM_RHEME    },
    /* IX:  (+1,+1, 0) Dicent Symbol Legisign           */
    { PSM_LEGISIGN,  PSM_SYMBOL, PSM_DICISIGN },
    /* X:   (+1,+1,+1) Argument Symbol Legisign         */
    { PSM_LEGISIGN,  PSM_SYMBOL, PSM_ARGUMENT },
};

static const char *g_class_names[10] = {
    "Rhematic Iconic Qualisign",       /* I   */
    "Rhematic Iconic Sinsign",         /* II  */
    "Rhematic Indexical Sinsign",      /* III */
    "Dicent Indexical Sinsign",        /* IV  */
    "Rhematic Iconic Legisign",        /* V   */
    "Rhematic Indexical Legisign",     /* VI  */
    "Dicent Indexical Legisign",       /* VII */
    "Rhematic Symbol Legisign",        /* VIII*/
    "Dicent Symbol Legisign",          /* IX  */
    "Argument Symbol Legisign",        /* X   */
};

/* ==== Initialization ==================================================== */

static inline int psm_init(psm_state_t *st)
{
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

/* ==== Sign Classification =============================================== */

static inline int psm_classify(psm_sign_class_t *cls, trit t1, trit t2, trit t3)
{
    if (!cls) return -1;
    /* Validate range */
    if (t1 < -1 || t1 > 1 || t2 < -1 || t2 > 1 || t3 < -1 || t3 > 1)
        return -1;

    cls->sign_itself       = t1;
    cls->sign_object       = t2;
    cls->sign_interpretant = t3;

    /* Check validity: t1 >= t2 >= t3 */
    if (t1 < t2 || t2 < t3)
        return -1;  /* Invalid combination */

    return 0;
}

static inline int psm_is_valid_class(const psm_sign_class_t *cls)
{
    if (!cls) return 0;
    if (cls->sign_itself < -1 || cls->sign_itself > 1) return 0;
    if (cls->sign_object < -1 || cls->sign_object > 1) return 0;
    if (cls->sign_interpretant < -1 || cls->sign_interpretant > 1) return 0;
    /* Peirce's constraint: I >= II >= III */
    return (cls->sign_itself >= cls->sign_object &&
            cls->sign_object >= cls->sign_interpretant) ? 1 : 0;
}

static inline int psm_class_id(const psm_sign_class_t *cls)
{
    if (!cls || !psm_is_valid_class(cls)) return 0;

    for (int i = 0; i < 10; i++) {
        if (g_valid_classes[i].sign_itself       == cls->sign_itself &&
            g_valid_classes[i].sign_object       == cls->sign_object &&
            g_valid_classes[i].sign_interpretant == cls->sign_interpretant) {
            return i + 1;  /* 1-based class ID */
        }
    }
    return 0; /* Should not happen for valid class */
}

static inline const char *psm_class_name(int id)
{
    if (id < 1 || id > 10) return "Invalid";
    return g_class_names[id - 1];
}

static inline int psm_enumerate_classes(psm_sign_class_t *out, int max)
{
    if (!out || max <= 0) return 0;
    int n = imin(10, max);
    memcpy(out, g_valid_classes, (size_t)n * sizeof(psm_sign_class_t));
    return n;
}

/* ==== Triadic Sign Relations ============================================ */

static inline int psm_create_relation(psm_state_t *st, int sign,
                        psm_object_t obj, psm_interpretant_t interp,
                        const psm_sign_class_t *cls)
{
    if (!st || !st->initialized || !cls) return -1;
    if (st->chain_len >= PSM_MAX_CHAIN) return -1;
    if (!psm_is_valid_class(cls)) return -1;

    int idx = st->chain_len;
    psm_sign_relation_t *rel = &st->chain[idx];
    rel->sign_value    = sign;
    rel->object        = obj;
    rel->interpretant  = interp;
    rel->classification = *cls;
    rel->class_id      = psm_class_id(cls);
    st->chain_len++;

    return idx;
}

static inline int psm_extend_chain(psm_state_t *st, psm_object_t obj,
                     psm_interpretant_t interp,
                     const psm_sign_class_t *cls)
{
    if (!st || !st->initialized || st->chain_len == 0) return -1;

    /* The dynamic interpretant of the previous sign becomes the new sign */
    int prev_interp = st->chain[st->chain_len - 1].interpretant.dynamic;

    return psm_create_relation(st, prev_interp, obj, interp, cls);
}

/* ==== Information Theory ================================================ */

static inline int psm_information(int extension, int intension)
{
    /* Information = Extension × Intension (CP 2.407-8)
       Both are ×1000, so info = ext * int / 1000 */
    return safe_mul_1000(extension, intension);
}

static inline int psm_information_inverse(int information, int known_dim)
{
    if (known_dim == 0) return -1;
    /* other_dim = information / known_dim (both ×1000)
       = (information * 1000) / known_dim */
    long long result = ((long long)information * 1000) / (long long)known_dim;
    if (result > 2000000000LL) return 2000000000;
    if (result < -2000000000LL) return -2000000000;
    return (int)result;
}

/* ==== Determination ===================================================== */

static inline int psm_triadic_determination(int object_val, int sign_val,
                              int interpretant_val)
{
    /*
     * Triadic determination measures the coherence of the sign relation.
     * Object determines Sign determines Interpretant, but this is not
     * a dyadic chain—it's irreducibly triadic.
     *
     * We model this as: how well does the interpretant "agree" with the
     * object-sign relation? Coherence = 1000 - normalized deviation.
     *
     * deviation = |interp - (obj + sign)/2| / max(|obj|, |sign|, |interp|, 1)
     */
    long long avg = ((long long)object_val + (long long)sign_val) / 2;
    long long dev = (long long)interpretant_val - avg;
    if (dev < 0) dev = -dev;

    int mx = iabs(object_val);
    if (iabs(sign_val) > mx) mx = iabs(sign_val);
    if (iabs(interpretant_val) > mx) mx = iabs(interpretant_val);
    if (mx == 0) mx = 1;

    int norm_dev = (int)((dev * 1000) / (long long)mx);
    int coherence = 1000 - imin(norm_dev, 1000);
    return coherence;
}

static inline int psm_reduction_thesis_loss(int object_val, int sign_val,
                              int interpretant_val)
{
    /*
     * Reduction Thesis: genuine triadic relations cannot be fully decomposed
     * into dyadic relations. Here we attempt the decomposition:
     *
     * Triadic: T(O, S, I)
     * Dyadic attempt: D1(O, S) and D2(S, I)
     *
     * The "lost" information is the mutual context that the triadic relation
     * carries—specifically, how interpretant relates to object *through*
     * the sign, not merely to the sign alone.
     *
     * Information lost = |T(O,S,I) - compose(D1(O,S), D2(S,I))|
     */
    /* Triadic coherence */
    int triadic = psm_triadic_determination(object_val, sign_val,
                                            interpretant_val);

    /* Dyadic decomposition: treat as two independent dyadic relations */
    long long d_os = (long long)iabs(object_val - sign_val);
    long long d_si = (long long)iabs(sign_val - interpretant_val);

    int mx = iabs(object_val);
    if (iabs(sign_val) > mx) mx = iabs(sign_val);
    if (iabs(interpretant_val) > mx) mx = iabs(interpretant_val);
    if (mx == 0) mx = 1;

    /* Dyadic coherence estimate: average of two pairwise coherences */
    int coh_os = 1000 - (int)imin((d_os * 1000) / (long long)mx, 1000);
    int coh_si = 1000 - (int)imin((d_si * 1000) / (long long)mx, 1000);
    int dyadic = (coh_os + coh_si) / 2;

    /* Loss: the triadic relation captures information the dyadic misses.
       For a genuine triadic relation (not degenerate), this is > 0. */
    int loss = iabs(triadic - dyadic);

    /* Additional: detect genuine triadicity via the sign of O-I relation
       conditioned on S. If O and I are on opposite sides of S, there is
       irreducible mediation. */
    long long oi_through_s = (long long)(object_val - sign_val) *
                             (long long)(sign_val - interpretant_val);
    if (oi_through_s > 0) {
        /* S mediates between O and I (both deviate same direction from S)
           → less genuine triadicity */
    } else if (oi_through_s < 0) {
        /* S genuinely mediates: O and I on opposite sides
           → more irreducible triadicity */
        loss += 100;
    }
    /* else oi_through_s == 0: degenerate case */

    return imin(loss, 1000);
}

static inline int psm_reduce_tetradic(int a, int b, int c, int d, int tri_out[2][3])
{
    if (!tri_out) return -1;

    /*
     * Reduce 4-adic R(a, b, c, d) into two triadic relations:
     *   T1(a, b, m) and T2(m, c, d)
     * where m is a mediating element (Peircean "identity node"):
     *   m = (b + c) / 2  (the connection point between the two triads).
     */
    int m = (b + c) / 2;
    tri_out[0][0] = a;
    tri_out[0][1] = b;
    tri_out[0][2] = m;
    tri_out[1][0] = m;
    tri_out[1][1] = c;
    tri_out[1][2] = d;
    return 0;
}

/* ==== Interpretant Analysis ============================================= */

psm_interpretant_t psm_analyze_interpretant(int sign_val, int obj_val)
{
    psm_interpretant_t it;

    /*
     * Immediate: quality of the impression the sign is fit to produce.
     * This is the potential, a Firstness—captured as the sign value itself
     * (what the sign "says" before we consider the object).
     */
    it.immediate = sign_val;

    /*
     * Dynamic: the actual effect of the sign on a mind, given the object.
     * This is a Secondness—the reaction: how the sign modifies understanding
     * of the object. Modeled as the midpoint nudged toward the object.
     */
    it.dynamic = (sign_val + obj_val) / 2;

    /*
     * Final: the effect the sign would have if inquiry were fully completed.
     * This is a Thirdness—the ideal convergence point. In an ideal semiosis,
     * the final interpretant is the object itself (truth).
     * We model it as object + correction toward sign's full information.
     */
    it.final_ = obj_val;

    return it;
}

static inline int psm_convergence(const psm_state_t *st)
{
    if (!st || st->chain_len < 2) return 0;

    /* How close is the last dynamic interpretant to its final interpretant,
       compared to the first? */
    const psm_sign_relation_t *first = &st->chain[0];
    const psm_sign_relation_t *last  = &st->chain[st->chain_len - 1];

    int dist_first = iabs(first->interpretant.dynamic -
                          first->interpretant.final_);
    int dist_last  = iabs(last->interpretant.dynamic -
                          last->interpretant.final_);

    if (dist_first == 0) return 1000; /* Already converged at start */

    /* Convergence ratio: how much closer the last is vs the first */
    int ratio = 1000 - (int)((long long)dist_last * 1000 /
                             (long long)dist_first);
    if (ratio < 0) ratio = 0;
    if (ratio > 1000) ratio = 1000;
    return ratio;
}

/* ==== Category Operations =============================================== */

static inline trit psm_category_ground(int quality)
{
    /* Firstness: the ground is the pure abstraction of a quality.
       Map to trit: positive → +1, negative → -1, zero → 0. */
    if (quality > 0)  return (trit)+1;
    if (quality < 0)  return (trit)-1;
    return (trit)0;
}

static inline trit psm_category_correlate(int relate, int correlate)
{
    /* Secondness: dyadic reaction between relate and correlate.
       The difference tells us the direction of resistance. */
    int diff = relate - correlate;
    return clamp_trit(diff > 0 ? 1 : (diff < 0 ? -1 : 0));
}

static inline trit psm_category_mediate(trit sign, trit object, trit interp)
{
    /* Thirdness: irreducible triadic mediation.
       Uses K3 consensus logic: if all three agree, return that value.
       If two agree, return that value (majority).
       If all different, return UNKNOWN (genuine mediation needed). */
    if (sign == object && object == interp) return sign;

    /* Majority of three ternary values */
    int sum = (int)sign + (int)object + (int)interp;
    if (sum >= 2)  return (trit)+1;
    if (sum <= -2) return (trit)-1;

    /* Check for two-agree cases */
    if (sign == object)  return sign;
    if (sign == interp)  return sign;
    if (object == interp) return object;

    /* All three different: genuine mediation, indeterminate */
    return TRIT_UNKNOWN;
}

/* ==== Hypoicon Classification =========================================== */

static inline int psm_hypoicon_classify(int resemblance, int relation, int parallelism)
{
    /*
     * Image    = simple quality dominates (resemblance highest).
     * Diagram  = internal relations dominate (relation highest).
     * Metaphor = parallelism dominates (parallelism highest).
     *
     * Ties broken by Peircean ordering: image < diagram < metaphor
     * (lower category wins in case of tie).
     */
    if (resemblance >= relation && resemblance >= parallelism)
        return PSM_IMAGE;
    if (relation >= resemblance && relation >= parallelism)
        return PSM_DIAGRAM;
    return PSM_METAPHOR;
}

/* ==== Adjacency ========================================================= */

static inline int psm_class_adjacency(int id_a, int id_b)
{
    if (id_a < 1 || id_a > 10 || id_b < 1 || id_b > 10) return -1;

    const psm_sign_class_t *a = &g_valid_classes[id_a - 1];
    const psm_sign_class_t *b = &g_valid_classes[id_b - 1];

    int shared = 0;
    if (a->sign_itself       == b->sign_itself)       shared++;
    if (a->sign_object       == b->sign_object)       shared++;
    if (a->sign_interpretant == b->sign_interpretant) shared++;

    return shared;
}

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_PEIRCE_SEMIOTIC_H */
