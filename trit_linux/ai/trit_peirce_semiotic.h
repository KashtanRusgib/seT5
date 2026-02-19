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

/* ==== API =============================================================== */

/**
 * @brief Initialize a semiosis engine state.
 * @param st  Pointer to state struct.
 * @return 0 on success, -1 on NULL.
 */
int psm_init(psm_state_t *st);

/* ---- Sign Classification ---------------------------------------------- */

/**
 * @brief Classify a sign by its three trichotomy values.
 * @param cls    Output sign class.
 * @param t1     Trichotomy I  (sign itself):      -1/0/+1.
 * @param t2     Trichotomy II (sign→object):      -1/0/+1.
 * @param t3     Trichotomy III (sign→interpretant): -1/0/+1.
 * @return 0 if valid, -1 if invalid combination.
 */
int psm_classify(psm_sign_class_t *cls, trit t1, trit t2, trit t3);

/**
 * @brief Check if a sign class is one of the 10 valid Peircean classes.
 * @param cls  Sign class to validate.
 * @return 1 if valid (a ≥ b ≥ c), 0 if invalid.
 */
int psm_is_valid_class(const psm_sign_class_t *cls);

/**
 * @brief Return the Peirce class ID (I–X) for a valid sign class.
 * @param cls  Sign class.
 * @return Class ID 1–10, or 0 if invalid.
 */
int psm_class_id(const psm_sign_class_t *cls);

/**
 * @brief Return human-readable name for a Peirce class ID (I–X).
 * @param id  Class ID (1–10).
 * @return Static string name, or "Invalid" if out of range.
 */
const char *psm_class_name(int id);

/**
 * @brief Enumerate all 10 valid sign classes.
 * @param out  Output array (must hold ≥ 10 elements).
 * @param max  Maximum elements to write.
 * @return Number of classes written (≤ min(10, max)).
 */
int psm_enumerate_classes(psm_sign_class_t *out, int max);

/* ---- Triadic Sign Relations ------------------------------------------- */

/**
 * @brief Create a triadic sign relation and add to chain.
 * @param st    Semiosis state.
 * @param sign  Sign value (×1000).
 * @param obj   Object values (immediate + dynamic, ×1000).
 * @param interp Interpretant values (imm/dyn/final, ×1000).
 * @param cls   Sign classification.
 * @return Chain index (≥0) on success, -1 on error.
 */
int psm_create_relation(psm_state_t *st, int sign,
                        psm_object_t obj, psm_interpretant_t interp,
                        const psm_sign_class_t *cls);

/**
 * @brief Extend the semiosis chain: prev interpretant → next sign.
 *
 * The dynamic interpretant of the last relation becomes the sign value
 * of the new relation, modeling Peirce's unlimited semiosis.
 *
 * @param st     Semiosis state.
 * @param obj    Next object.
 * @param interp Next interpretant.
 * @param cls    Next sign classification.
 * @return New chain index (≥0), or -1 on error.
 */
int psm_extend_chain(psm_state_t *st, psm_object_t obj,
                     psm_interpretant_t interp,
                     const psm_sign_class_t *cls);

/* ---- Information Theory ----------------------------------------------- */

/**
 * @brief Compute information = extension × intension (Peirce CP 2.407–8).
 * @param extension  Breadth / denotation (×1000).
 * @param intension  Depth / comprehension (×1000).
 * @return Information value (×1000, clamped to avoid overflow).
 */
int psm_information(int extension, int intension);

/**
 * @brief Inverse information: given info and one dimension, find the other.
 *
 * If extension × intension = information (constant), increasing intension
 * must decrease extension (and vice versa).
 *
 * @param information  Total information (×1000).
 * @param known_dim    Known dimension value (×1000, must be > 0).
 * @return Other dimension (×1000), or -1 on error.
 */
int psm_information_inverse(int information, int known_dim);

/* ---- Determination (Triadic) ------------------------------------------ */

/**
 * @brief Triadic determination: object → sign → interpretant.
 *
 * Models how the object determines the sign to determine the interpretant.
 * This is irreducibly triadic, not a succession of dyadic events.
 *
 * @param object_val       Object value (×1000).
 * @param sign_val         Sign value (×1000).
 * @param interpretant_val Interpretant value (×1000).
 * @return Determination strength (×1000): how well the triad coheres.
 */
int psm_triadic_determination(int object_val, int sign_val,
                              int interpretant_val);

/**
 * @brief Attempt dyadic decomposition (should lose information).
 *
 * Demonstrates the Reduction Thesis: genuine triadic relations cannot
 * be fully analyzed into dyadic relations. Returns the information lost.
 *
 * @param object_val       Object value (×1000).
 * @param sign_val         Sign value (×1000).
 * @param interpretant_val Interpretant value (×1000).
 * @return Information lost by dyadic decomposition (×1000, > 0 for
 *         genuine triadic relations).
 */
int psm_reduction_thesis_loss(int object_val, int sign_val,
                              int interpretant_val);

/**
 * @brief Reduce a tetradic relation to triadic + lower.
 *
 * Demonstrates the other half of the Reduction Thesis: all 4-adic
 * relations can be decomposed into triadic and lower.
 *
 * @param a,b,c,d  Four relation values (×1000).
 * @param tri_out  Output: two triadic sub-relations (array of 2×3 ints).
 * @return 0 on success (tetradic fully reduced), -1 on error.
 */
int psm_reduce_tetradic(int a, int b, int c, int d, int tri_out[2][3]);

/* ---- Interpretant Analysis -------------------------------------------- */

/**
 * @brief Analyze a sign–object pair into immediate/dynamic/final interpretants.
 *
 * Immediate = quality of impression (|sign - object| as potential).
 * Dynamic   = actual effect: sign modified by object.
 * Final     = norm: what inquiry would converge to.
 *
 * @param sign_val  Sign value (×1000).
 * @param obj_val   Object value (×1000).
 * @return Interpretant triple.
 */
psm_interpretant_t psm_analyze_interpretant(int sign_val, int obj_val);

/**
 * @brief Check convergence toward final interpretant.
 *
 * In a semiosis chain, later interpretants should approach the final
 * interpretant (truth as ideal final opinion).
 *
 * @param st  Semiosis state with populated chain.
 * @return Convergence metric (×1000): ratio of how close the last
 *         dynamic interpretant is to the final, vs the first.
 *         Higher = more convergent. 1000 = perfectly converged.
 */
int psm_convergence(const psm_state_t *st);

/* ---- Category Operations (Ternary Logic) ------------------------------ */

/**
 * @brief Firstness ground: pure abstraction of a quality.
 *
 * Returns the monadic category value—the quality in itself,
 * irrespective of relation to anything else.
 *
 * @param quality  Input quality value (×1000).
 * @return Ground value: sign(quality) as trit.
 */
trit psm_category_ground(int quality);

/**
 * @brief Secondness correlate: dyadic reaction between relate and correlate.
 * @param relate     First element (×1000).
 * @param correlate  Second element (×1000).
 * @return Reaction value: (relate - correlate) clamped to trit.
 */
trit psm_category_correlate(int relate, int correlate);

/**
 * @brief Thirdness mediation: irreducible triadic relation.
 *
 * The mediating sign connects object and interpretant.
 * Uses K3 consensus logic: agreement yields that value, else unknown.
 *
 * @param sign   Sign trit.
 * @param object Object trit.
 * @param interp Interpretant trit.
 * @return Mediation trit (consensus of the three, or UNKNOWN).
 */
trit psm_category_mediate(trit sign, trit object, trit interp);

/* ---- Hypoicon Classification ------------------------------------------ */

/**
 * @brief Classify a hypoicon (icon apart from attached indices).
 *
 * Image    = depends on simple quality (resemblance dominant).
 * Diagram  = internal relations represent by analogy.
 * Metaphor = parallelism in something else.
 *
 * @param resemblance  Quality similarity score (×1000).
 * @param relation     Structural/relational similarity (×1000).
 * @param parallelism  Metaphorical parallelism (×1000).
 * @return PSM_IMAGE, PSM_DIAGRAM, or PSM_METAPHOR.
 */
int psm_hypoicon_classify(int resemblance, int relation, int parallelism);

/* ---- Adjacency in the Ten-Class Triangle ------------------------------ */

/**
 * @brief Check if two sign classes are adjacent in Peirce's triangle.
 *
 * Adjacent classes share at least one trichotomy value. In Peirce's
 * MS 540 triangular arrangement, most adjacent pairs share two
 * aspects, but three pairs (II&VI, VI&IX, III&VII) share only one.
 *
 * @param id_a  First class ID (1–10).
 * @param id_b  Second class ID (1–10).
 * @return Number of shared trichotomy values (0–3), or -1 on error.
 */
int psm_class_adjacency(int id_a, int id_b);

#ifdef __cplusplus
}
#endif

#endif /* SET6_TRIT_PEIRCE_SEMIOTIC_H */
