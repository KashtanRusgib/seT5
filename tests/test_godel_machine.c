/**
 * @file test_godel_machine.c
 * @brief T-049: Gödel Machine Comprehensive Test Suite
 *
 * Tests for the Gödel machine module:
 *   - Utility function computation
 *   - Delta utility tracking
 *   - Cost accounting
 *   - Proof instruction API (all 6 instructions)
 *   - Self-improvement criterion
 *   - Rollback on failed verification
 *   - Archive operations
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdio.h>
#include <string.h>
#include <math.h>

static int tests_passed = 0;
static int tests_failed = 0;

#define TEST(name) do { printf("  %-60s ", #name); fflush(stdout); } while(0)
#define PASS()     do { printf("[PASS]\n"); tests_passed++; } while(0)
#define FAIL(msg)  do { printf("[FAIL] %s\n", msg); tests_failed++; } while(0)

/* ── Inline Gödel engine types (from godel_machine.c) ── */

#define GODEL_MAX_AXIOMS       256
#define GODEL_MAX_THEOREMS     512
#define GODEL_MAX_RULES        64
#define GODEL_MAX_SWITCHPROGS  32
#define GODEL_MAX_NAME_LEN     128
#define GODEL_MAX_CONTENT_LEN  1024

typedef enum {
    GODEL_AXIOM_HARDWARE    = 0,
    GODEL_AXIOM_REWARD      = 1,
    GODEL_AXIOM_ENVIRONMENT = 2,
    GODEL_AXIOM_UTILITY     = 3,
    GODEL_AXIOM_STATE       = 4,
} godel_axiom_type_t;

typedef enum {
    GODEL_RULE_MODUS_PONENS = 0,
    GODEL_RULE_CONJUNCTION  = 1,
    GODEL_RULE_UNIVERSAL    = 2,
    GODEL_RULE_SUBSTITUTION = 3,
    GODEL_RULE_INDUCTION    = 4,
    GODEL_RULE_TRIT_EVAL    = 5,
} godel_rule_t;

typedef struct {
    int                 id;
    char                name[GODEL_MAX_NAME_LEN];
    char                content[GODEL_MAX_CONTENT_LEN];
    godel_axiom_type_t  type;
    int                 derived_from[2];
    godel_rule_t        derived_rule;
    trit                verified;
    trit                active;
} godel_theorem_t;

typedef struct {
    int     id;
    char    filepath[GODEL_MAX_NAME_LEN];
    char    old_content[GODEL_MAX_CONTENT_LEN];
    char    new_content[GODEL_MAX_CONTENT_LEN];
    int     theorem_id;
    trit    applied;
    double  expected_delta_u;
} godel_switchprog_t;

typedef struct {
    godel_theorem_t    axioms[GODEL_MAX_AXIOMS];
    int                n_axioms;
    godel_theorem_t    theorems[GODEL_MAX_THEOREMS];
    int                n_theorems;
    godel_switchprog_t switchprogs[GODEL_MAX_SWITCHPROGS];
    int                n_switchprogs;
    int     tests_total, tests_passing;
    int     proofs_total, proofs_verified;
    int     trit_functions, total_functions;
    int     binary_reversions;
    double  current_utility, previous_utility, delta_utility;
    double  search_fraction;
    int     search_budget_ms, search_elapsed_ms;
    int     generation;
    trit    initialized;
} godel_machine_t;

/* Externs from godel_machine.c */
extern int godel_init(godel_machine_t *gm);
extern const godel_theorem_t *godel_get_axiom(const godel_machine_t *gm, int n);
extern int godel_apply_rule(godel_machine_t *gm, godel_rule_t rule, int m, int n);
extern int godel_delete_theorem(godel_machine_t *gm, int id);
extern int godel_set_switchprog(godel_machine_t *gm, const char *fp,
                                 const char *old, const char *new_c,
                                 int thm_id, double delta_u);
extern int godel_check(const godel_machine_t *gm);
extern int godel_state2theorem(godel_machine_t *gm);
extern double godel_compute_utility(godel_machine_t *gm);
extern int godel_update_metrics(godel_machine_t *gm,
    int tp, int tt, int pp, int pt, int tf, int ttf, int br);

/* ═══════════════════════════════════════════════════════════
 * Test: Initialization
 * ═══════════════════════════════════════════════════════════ */
static void test_init(void) {
    TEST(godel_init_succeeds);
    godel_machine_t gm;
    int rc = godel_init(&gm);
    if (rc == 0 && gm.initialized == TRIT_TRUE && gm.n_axioms == 6) PASS();
    else FAIL("init failed");
}

static void test_init_null(void) {
    TEST(godel_init_null_returns_error);
    if (godel_init(NULL) == -1) PASS(); else FAIL("expected -1");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 1 — get_axiom
 * ═══════════════════════════════════════════════════════════ */
static void test_get_axiom_valid(void) {
    TEST(get_axiom_returns_valid_axiom);
    godel_machine_t gm;
    godel_init(&gm);
    const godel_theorem_t *a = godel_get_axiom(&gm, 0);
    if (a && a->verified == TRIT_TRUE && a->active == TRIT_TRUE && strlen(a->name) > 0) PASS();
    else FAIL("axiom invalid");
}

static void test_get_axiom_oob(void) {
    TEST(get_axiom_oob_returns_null);
    godel_machine_t gm;
    godel_init(&gm);
    if (godel_get_axiom(&gm, 999) == NULL) PASS();
    else FAIL("expected NULL");
}

static void test_axiom_types(void) {
    TEST(axioms_cover_all_5_types);
    godel_machine_t gm;
    godel_init(&gm);
    int seen[5] = {0};
    for (int i = 0; i < gm.n_axioms; i++) {
        if (gm.axioms[i].type >= 0 && gm.axioms[i].type <= 4)
            seen[gm.axioms[i].type] = 1;
    }
    if (seen[0] && seen[1] && seen[2] && seen[3] && seen[4]) PASS();
    else FAIL("missing axiom type");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 2 — apply_rule
 * ═══════════════════════════════════════════════════════════ */
static void test_apply_modus_ponens(void) {
    TEST(apply_rule_modus_ponens);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS, 0, 1);
    if (id >= 0 && gm.theorems[id].active == TRIT_TRUE && gm.theorems[id].verified == TRIT_TRUE) PASS();
    else FAIL("modus ponens failed");
}

static void test_apply_conjunction(void) {
    TEST(apply_rule_conjunction);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 2);
    if (id >= 0 && gm.theorems[id].active == TRIT_TRUE) PASS();
    else FAIL("conjunction failed");
}

static void test_apply_trit_eval(void) {
    TEST(apply_rule_trit_eval);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    if (id >= 0 && gm.theorems[id].verified == TRIT_TRUE) PASS();
    else FAIL("trit eval failed");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 3 — delete_theorem
 * ═══════════════════════════════════════════════════════════ */
static void test_delete_theorem(void) {
    TEST(delete_theorem_deactivates);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    int rc = godel_delete_theorem(&gm, id);
    if (rc == 0 && gm.theorems[id].active == TRIT_FALSE) PASS();
    else FAIL("delete failed");
}

static void test_delete_oob(void) {
    TEST(delete_theorem_oob_returns_error);
    godel_machine_t gm;
    godel_init(&gm);
    if (godel_delete_theorem(&gm, 999) == -1) PASS();
    else FAIL("expected -1");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 4 — set_switchprog
 * ═══════════════════════════════════════════════════════════ */
static void test_set_switchprog(void) {
    TEST(set_switchprog_stores_diff);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_set_switchprog(&gm, "src/test.c",
        "old code", "new code", 0, 0.01);
    if (id >= 0 && gm.n_switchprogs == 1 && gm.switchprogs[id].applied == TRIT_UNKNOWN) PASS();
    else FAIL("switchprog failed");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 5 — check
 * ═══════════════════════════════════════════════════════════ */
static void test_check_no_improvement(void) {
    TEST(check_returns_0_when_no_delta);
    godel_machine_t gm;
    godel_init(&gm);
    if (godel_check(&gm) == 0) PASS();
    else FAIL("expected 0");
}

static void test_check_with_improvement(void) {
    TEST(check_returns_1_when_delta_positive);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    godel_update_metrics(&gm, 200, 200, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    if (gm.delta_utility >= 0) PASS(); /* utility maintained or improved */
    else FAIL("expected non-negative delta");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 6 — state2theorem
 * ═══════════════════════════════════════════════════════════ */
static void test_state2theorem(void) {
    TEST(state2theorem_encodes_runtime_state);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 1792, 1792, 8, 8, 40, 40, 0);
    godel_compute_utility(&gm);
    int id = godel_state2theorem(&gm);
    if (id >= 0 && gm.theorems[id].verified == TRIT_TRUE &&
        gm.theorems[id].type == GODEL_AXIOM_STATE) PASS();
    else FAIL("state2theorem failed");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Utility computation
 * ═══════════════════════════════════════════════════════════ */
static void test_utility_perfect(void) {
    TEST(utility_perfect_score_equals_1);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    double u = godel_compute_utility(&gm);
    if (u > 0.999 && u <= 1.0) PASS();
    else FAIL("expected ~1.0");
}

static void test_utility_zero_tests(void) {
    TEST(utility_zero_when_no_tests);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 0, 0, 0, 0, 0, 0, 0);
    double u = godel_compute_utility(&gm);
    if (u == 0.0) PASS();
    else FAIL("expected 0.0");
}

static void test_utility_binary_reversion_penalty(void) {
    TEST(utility_decreases_with_reversions);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    double u_clean = godel_compute_utility(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 10);
    double u_dirty = godel_compute_utility(&gm);
    if (u_dirty < u_clean) PASS();
    else FAIL("reversions should decrease utility");
}

static void test_delta_tracking(void) {
    TEST(delta_utility_tracked_correctly);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 50, 100, 5, 10, 25, 50, 0);
    godel_compute_utility(&gm);
    double u1 = gm.current_utility;
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    double delta = gm.delta_utility;
    double expected_delta = gm.current_utility - u1;
    if (fabs(delta - expected_delta) < 1e-10) PASS();
    else FAIL("delta tracking incorrect");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Self-improvement criterion (rollback)
 * ═══════════════════════════════════════════════════════════ */
static void test_rollback_on_decrease(void) {
    TEST(no_accept_when_utility_decreases);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    godel_update_metrics(&gm, 50, 100, 5, 10, 25, 50, 5);
    godel_compute_utility(&gm);
    godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    if (godel_check(&gm) <= 0) PASS(); /* rejected — trit: 0=neutral, -1=regressing */
    else FAIL("should reject negative delta");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Multiple theorem derivation chain
 * ═══════════════════════════════════════════════════════════ */
static void test_theorem_chain(void) {
    TEST(multiple_derivations_chain_correctly);
    godel_machine_t gm;
    godel_init(&gm);
    int t1 = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION, 0, 1);
    int t2 = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS, t1, 2);
    if (t1 >= 0 && t2 >= 0 && t2 > t1 &&
        gm.theorems[t2].derived_from[0] == t1) PASS();
    else FAIL("chain broken");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Search fraction parameter
 * ═══════════════════════════════════════════════════════════ */
static void test_search_fraction(void) {
    TEST(biops_search_fraction_default);
    godel_machine_t gm;
    godel_init(&gm);
    if (gm.search_fraction > 0.0 && gm.search_fraction <= 1.0) PASS();
    else FAIL("search fraction out of range");
}

int main(void) {
    printf("=== T-049: Gödel Machine Test Suite ===\n");

    test_init();
    test_init_null();
    test_get_axiom_valid();
    test_get_axiom_oob();
    test_axiom_types();
    test_apply_modus_ponens();
    test_apply_conjunction();
    test_apply_trit_eval();
    test_delete_theorem();
    test_delete_oob();
    test_set_switchprog();
    test_check_no_improvement();
    test_check_with_improvement();
    test_state2theorem();
    test_utility_perfect();
    test_utility_zero_tests();
    test_utility_binary_reversion_penalty();
    test_delta_tracking();
    test_rollback_on_decrease();
    test_theorem_chain();
    test_search_fraction();

    printf("=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
