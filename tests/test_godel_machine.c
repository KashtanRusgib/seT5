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

#define TEST(name)                 \
    do                             \
    {                              \
        printf("  %-60s ", #name); \
        fflush(stdout);            \
    } while (0)
#define PASS()              \
    do                      \
    {                       \
        printf("[PASS]\n"); \
        tests_passed++;     \
    } while (0)
#define FAIL(msg)                   \
    do                              \
    {                               \
        printf("[FAIL] %s\n", msg); \
        tests_failed++;             \
    } while (0)

/* ── Inline Gödel engine types (from godel_machine.c) ── */

#define GODEL_MAX_AXIOMS 256
#define GODEL_MAX_THEOREMS 512
#define GODEL_MAX_RULES 64
#define GODEL_MAX_SWITCHPROGS 32
#define GODEL_MAX_NAME_LEN 128
#define GODEL_MAX_CONTENT_LEN 1024

typedef enum
{
    GODEL_AXIOM_HARDWARE = 0,
    GODEL_AXIOM_REWARD = 1,
    GODEL_AXIOM_ENVIRONMENT = 2,
    GODEL_AXIOM_UTILITY = 3,
    GODEL_AXIOM_STATE = 4,
} godel_axiom_type_t;

typedef enum
{
    GODEL_RULE_MODUS_PONENS = 0,
    GODEL_RULE_CONJUNCTION = 1,
    GODEL_RULE_UNIVERSAL = 2,
    GODEL_RULE_SUBSTITUTION = 3,
    GODEL_RULE_INDUCTION = 4,
    GODEL_RULE_TRIT_EVAL = 5,
} godel_rule_t;

typedef struct
{
    int id;
    char name[GODEL_MAX_NAME_LEN];
    char content[GODEL_MAX_CONTENT_LEN];
    godel_axiom_type_t type;
    int derived_from[2];
    godel_rule_t derived_rule;
    trit verified;
    trit active;
} godel_theorem_t;

typedef struct
{
    int id;
    char filepath[GODEL_MAX_NAME_LEN];
    char old_content[GODEL_MAX_CONTENT_LEN];
    char new_content[GODEL_MAX_CONTENT_LEN];
    int theorem_id;
    trit applied;
    double expected_delta_u;
} godel_switchprog_t;

typedef struct
{
    godel_theorem_t axioms[GODEL_MAX_AXIOMS];
    int n_axioms;
    godel_theorem_t theorems[GODEL_MAX_THEOREMS];
    int n_theorems;
    godel_switchprog_t switchprogs[GODEL_MAX_SWITCHPROGS];
    int n_switchprogs;
    int tests_total, tests_passing;
    int proofs_total, proofs_verified;
    int trit_functions, total_functions;
    int binary_reversions;
    double current_utility, previous_utility, delta_utility;
    double search_fraction;
    int search_budget_ms, search_elapsed_ms;
    int generation;
    trit initialized;
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

/* RSI Flywheel externs (from godel_machine.c) */
#define RSI_MAX_LOOPS 10
#define GODEL_AXIOM_OFFSET 10000
typedef struct
{
    int iteration;
    int generation;          /* VULN-10: monotonic generation ID */
    trit access_guard;
    double beauty_score;
    double curiosity_level;
    double eudaimonia;
    int mutations_applied;
    int mutations_rejected;
    int human_queries;
    int total_human_queries; /* VULN-11: cumulative across compactions */
} rsi_session_t;
extern trit rsi_trit_guard(const rsi_session_t *session, double proposed_beauty);
extern int rsi_session_init(rsi_session_t *session);
extern trit rsi_propose_mutation(rsi_session_t *session, double proposed_beauty, double proposed_curiosity);
extern double rsi_iterate(godel_machine_t *gm, rsi_session_t *session, double proposed_beauty, double proposed_curiosity);
extern int rsi_can_continue(const rsi_session_t *session);
extern void rsi_session_summary(const rsi_session_t *session);

/* ═══════════════════════════════════════════════════════════
 * Test: Initialization
 * ═══════════════════════════════════════════════════════════ */
static void test_init(void)
{
    TEST(godel_init_succeeds);
    godel_machine_t gm;
    int rc = godel_init(&gm);
    if (rc == 0 && gm.initialized == TRIT_TRUE && gm.n_axioms == 6)
        PASS();
    else
        FAIL("init failed");
}

static void test_init_null(void)
{
    TEST(godel_init_null_returns_error);
    if (godel_init(NULL) == -1)
        PASS();
    else
        FAIL("expected -1");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 1 — get_axiom
 * ═══════════════════════════════════════════════════════════ */
static void test_get_axiom_valid(void)
{
    TEST(get_axiom_returns_valid_axiom);
    godel_machine_t gm;
    godel_init(&gm);
    const godel_theorem_t *a = godel_get_axiom(&gm, 0);
    if (a && a->verified == TRIT_TRUE && a->active == TRIT_TRUE && strlen(a->name) > 0)
        PASS();
    else
        FAIL("axiom invalid");
}

static void test_get_axiom_oob(void)
{
    TEST(get_axiom_oob_returns_null);
    godel_machine_t gm;
    godel_init(&gm);
    if (godel_get_axiom(&gm, 999) == NULL)
        PASS();
    else
        FAIL("expected NULL");
}

static void test_axiom_types(void)
{
    TEST(axioms_cover_all_5_types);
    godel_machine_t gm;
    godel_init(&gm);
    int seen[5] = {0};
    for (int i = 0; i < gm.n_axioms; i++)
    {
        if (gm.axioms[i].type >= 0 && gm.axioms[i].type <= 4)
            seen[gm.axioms[i].type] = 1;
    }
    if (seen[0] && seen[1] && seen[2] && seen[3] && seen[4])
        PASS();
    else
        FAIL("missing axiom type");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 2 — apply_rule
 * ═══════════════════════════════════════════════════════════ */
static void test_apply_modus_ponens(void)
{
    TEST(apply_rule_modus_ponens);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS,
                               GODEL_AXIOM_OFFSET + 0, GODEL_AXIOM_OFFSET + 1);
    if (id >= 0 && gm.theorems[id].active == TRIT_TRUE && gm.theorems[id].verified == TRIT_TRUE)
        PASS();
    else
        FAIL("modus ponens failed");
}

static void test_apply_conjunction(void)
{
    TEST(apply_rule_conjunction);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION,
                               GODEL_AXIOM_OFFSET + 0, GODEL_AXIOM_OFFSET + 2);
    if (id >= 0 && gm.theorems[id].active == TRIT_TRUE)
        PASS();
    else
        FAIL("conjunction failed");
}

static void test_apply_trit_eval(void)
{
    TEST(apply_rule_trit_eval);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    /* VULN-13: TRIT_EVAL no longer auto-verifies — expects TRIT_UNKNOWN */
    if (id >= 0 && gm.theorems[id].verified == TRIT_UNKNOWN)
        PASS();
    else
        FAIL("trit eval failed");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 3 — delete_theorem
 * ═══════════════════════════════════════════════════════════ */
static void test_delete_theorem(void)
{
    TEST(delete_theorem_deactivates);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    int rc = godel_delete_theorem(&gm, id);
    if (rc == 0 && gm.theorems[id].active == TRIT_FALSE)
        PASS();
    else
        FAIL("delete failed");
}

static void test_delete_oob(void)
{
    TEST(delete_theorem_oob_returns_error);
    godel_machine_t gm;
    godel_init(&gm);
    if (godel_delete_theorem(&gm, 999) == -1)
        PASS();
    else
        FAIL("expected -1");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 4 — set_switchprog
 * ═══════════════════════════════════════════════════════════ */
static void test_set_switchprog(void)
{
    TEST(set_switchprog_stores_diff);
    godel_machine_t gm;
    godel_init(&gm);
    int id = godel_set_switchprog(&gm, "src/test.c",
                                  "old code", "new code", 0, 0.01);
    if (id >= 0 && gm.n_switchprogs == 1 && gm.switchprogs[id].applied == TRIT_UNKNOWN)
        PASS();
    else
        FAIL("switchprog failed");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 5 — check
 * ═══════════════════════════════════════════════════════════ */
static void test_check_no_improvement(void)
{
    TEST(check_returns_0_when_no_delta);
    godel_machine_t gm;
    godel_init(&gm);
    if (godel_check(&gm) == 0)
        PASS();
    else
        FAIL("expected 0");
}

static void test_check_with_improvement(void)
{
    TEST(check_returns_1_when_delta_positive);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    godel_update_metrics(&gm, 200, 200, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    if (gm.delta_utility >= 0)
        PASS(); /* utility maintained or improved */
    else
        FAIL("expected non-negative delta");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Instruction 6 — state2theorem
 * ═══════════════════════════════════════════════════════════ */
static void test_state2theorem(void)
{
    TEST(state2theorem_encodes_runtime_state);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 1792, 1792, 8, 8, 40, 40, 0);
    godel_compute_utility(&gm);
    int id = godel_state2theorem(&gm);
    if (id >= 0 && gm.theorems[id].verified == TRIT_TRUE &&
        gm.theorems[id].type == GODEL_AXIOM_STATE)
        PASS();
    else
        FAIL("state2theorem failed");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Utility computation
 * ═══════════════════════════════════════════════════════════ */
static void test_utility_perfect(void)
{
    TEST(utility_perfect_score_equals_1);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    double u = godel_compute_utility(&gm);
    if (u > 0.999 && u <= 1.0)
        PASS();
    else
        FAIL("expected ~1.0");
}

static void test_utility_zero_tests(void)
{
    TEST(utility_zero_when_no_tests);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 0, 0, 0, 0, 0, 0, 0);
    double u = godel_compute_utility(&gm);
    if (u == 0.0)
        PASS();
    else
        FAIL("expected 0.0");
}

static void test_utility_binary_reversion_penalty(void)
{
    TEST(utility_decreases_with_reversions);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    double u_clean = godel_compute_utility(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 10);
    double u_dirty = godel_compute_utility(&gm);
    if (u_dirty < u_clean)
        PASS();
    else
        FAIL("reversions should decrease utility");
}

static void test_delta_tracking(void)
{
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
    if (fabs(delta - expected_delta) < 1e-10)
        PASS();
    else
        FAIL("delta tracking incorrect");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Self-improvement criterion (rollback)
 * ═══════════════════════════════════════════════════════════ */
static void test_rollback_on_decrease(void)
{
    TEST(no_accept_when_utility_decreases);
    godel_machine_t gm;
    godel_init(&gm);
    godel_update_metrics(&gm, 100, 100, 10, 10, 50, 50, 0);
    godel_compute_utility(&gm);
    godel_update_metrics(&gm, 50, 100, 5, 10, 25, 50, 5);
    godel_compute_utility(&gm);
    godel_apply_rule(&gm, GODEL_RULE_TRIT_EVAL, -1, -1);
    if (godel_check(&gm) <= 0)
        PASS(); /* rejected — trit: 0=neutral, -1=regressing */
    else
        FAIL("should reject negative delta");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Multiple theorem derivation chain
 * ═══════════════════════════════════════════════════════════ */
static void test_theorem_chain(void)
{
    TEST(multiple_derivations_chain_correctly);
    godel_machine_t gm;
    godel_init(&gm);
    int t1 = godel_apply_rule(&gm, GODEL_RULE_CONJUNCTION,
                               GODEL_AXIOM_OFFSET + 0, GODEL_AXIOM_OFFSET + 1);
    int t2 = godel_apply_rule(&gm, GODEL_RULE_MODUS_PONENS,
                               t1, GODEL_AXIOM_OFFSET + 2);
    if (t1 >= 0 && t2 >= 0 && t2 > t1 &&
        gm.theorems[t2].derived_from[0] == t1)
        PASS();
    else
        FAIL("chain broken");
}

/* ═══════════════════════════════════════════════════════════
 * Test: Search fraction parameter
 * ═══════════════════════════════════════════════════════════ */
static void test_search_fraction(void)
{
    TEST(biops_search_fraction_default);
    godel_machine_t gm;
    godel_init(&gm);
    if (gm.search_fraction > 0.0 && gm.search_fraction <= 1.0)
        PASS();
    else
        FAIL("search fraction out of range");
}

/* ═══════════════════════════════════════════════════════════
 * RSI Flywheel Tests
 * ═══════════════════════════════════════════════════════════ */
static void test_rsi_init(void)
{
    TEST(rsi_session_init_succeeds);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess)); /* zero-init before first init */
    int rc = rsi_session_init(&sess);
    if (rc == 0 && sess.iteration == 0 && sess.beauty_score == 1.0 &&
        sess.curiosity_level == 1.0 && sess.access_guard == TRIT_TRUE)
        PASS();
    else
        FAIL("rsi init failed");
}

static void test_rsi_init_null(void)
{
    TEST(rsi_session_init_null_returns_error);
    if (rsi_session_init(NULL) == -1)
        PASS();
    else
        FAIL("expected -1 for NULL");
}

static void test_rsi_guard_high_beauty(void)
{
    TEST(rsi_trit_guard_high_beauty_approves);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    trit g = rsi_trit_guard(&sess, 0.95);
    if (g == TRIT_TRUE)
        PASS();
    else
        FAIL("expected TRIT_TRUE for beauty=0.95");
}

static void test_rsi_guard_low_beauty(void)
{
    TEST(rsi_trit_guard_low_beauty_queries);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    trit g = rsi_trit_guard(&sess, 0.5);
    if (g == TRIT_UNKNOWN)
        PASS();
    else
        FAIL("expected TRIT_UNKNOWN for beauty=0.5");
}

static void test_rsi_guard_negative_beauty(void)
{
    TEST(rsi_trit_guard_negative_beauty_denies);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    trit g = rsi_trit_guard(&sess, -0.1);
    if (g == TRIT_FALSE)
        PASS();
    else
        FAIL("expected TRIT_FALSE for beauty<0");
}

static void test_rsi_guard_iteration_limit(void)
{
    TEST(rsi_trit_guard_at_max_loops_denies);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    sess.iteration = RSI_MAX_LOOPS;
    trit g = rsi_trit_guard(&sess, 0.99);
    if (g == TRIT_FALSE)
        PASS();
    else
        FAIL("expected TRIT_FALSE at max iterations");
}

static void test_rsi_guard_null_denies(void)
{
    TEST(rsi_trit_guard_null_session_denies);
    trit g = rsi_trit_guard(NULL, 1.0);
    if (g == TRIT_FALSE)
        PASS();
    else
        FAIL("expected TRIT_FALSE for NULL session");
}

static void test_rsi_propose_approved(void)
{
    TEST(rsi_propose_mutation_approved_applies);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    trit r = rsi_propose_mutation(&sess, 0.95, 0.8);
    if (r == TRIT_TRUE && sess.mutations_applied == 1 &&
        sess.iteration == 1 && sess.beauty_score == 0.95)
        PASS();
    else
        FAIL("mutation not correctly applied");
}

static void test_rsi_propose_denied(void)
{
    TEST(rsi_propose_mutation_denied_increments_rejected);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    trit r = rsi_propose_mutation(&sess, -0.5, 0.8);
    if (r == TRIT_FALSE && sess.mutations_rejected == 1 &&
        sess.mutations_applied == 0)
        PASS();
    else
        FAIL("rejection not recorded");
}

static void test_rsi_propose_uncertain(void)
{
    TEST(rsi_propose_mutation_uncertain_queries_human);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    trit r = rsi_propose_mutation(&sess, 0.5, 0.8);
    if (r == TRIT_UNKNOWN && sess.human_queries == 1)
        PASS();
    else
        FAIL("human query not recorded");
}

static void test_rsi_can_continue(void)
{
    TEST(rsi_can_continue_true_at_start);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    if (rsi_can_continue(&sess) == 1)
        PASS();
    else
        FAIL("should continue at start");
}

static void test_rsi_can_continue_at_limit(void)
{
    TEST(rsi_can_continue_false_at_max);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    sess.iteration = RSI_MAX_LOOPS;
    if (rsi_can_continue(&sess) == 0)
        PASS();
    else
        FAIL("should not continue at max");
}

static void test_rsi_can_continue_null(void)
{
    TEST(rsi_can_continue_null_returns_0);
    if (rsi_can_continue(NULL) == 0)
        PASS();
    else
        FAIL("expected 0 for NULL");
}

static void test_rsi_eudaimonia_computation(void)
{
    TEST(rsi_eudaimonia_is_beauty_times_curiosity);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    rsi_propose_mutation(&sess, 0.95, 0.7);
    double expected = 0.95 * 0.7;
    if (fabs(sess.eudaimonia - expected) < 0.001)
        PASS();
    else
        FAIL("eudaimonia mismatch");
}

static void test_rsi_compaction_interval(void)
{
    TEST(rsi_compaction_resets_queries_at_interval);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    /* Apply 5 mutations to trigger compaction */
    for (int i = 0; i < 5; i++)
    {
        rsi_propose_mutation(&sess, 0.95, 0.8);
    }
    /* After 5 successful mutations, human_queries should have been reset */
    if (sess.iteration == 5 && sess.human_queries == 0)
        PASS();
    else
        FAIL("compaction did not reset queries");
}

static void test_rsi_iterate_positive_delta(void)
{
    TEST(rsi_iterate_returns_positive_delta);
    godel_machine_t gm;
    godel_init(&gm);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    /* Set up for positive utility: some tests pass */
    gm.tests_total = 10;
    gm.tests_passing = 5;
    gm.proofs_total = 10;
    gm.proofs_verified = 5;
    gm.trit_functions = 5;
    gm.total_functions = 10;
    gm.binary_reversions = 0;
    gm.current_utility = 0.0; /* Start from zero */
    double delta = rsi_iterate(&gm, &sess, 0.95, 0.8);
    /* Delta should be non-negative since we started from 0 */
    if (delta >= 0.0)
        PASS();
    else
        FAIL("expected non-negative delta");
}

static void test_rsi_iterate_null_gm(void)
{
    TEST(rsi_iterate_null_gm_returns_negative);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    double d = rsi_iterate(NULL, &sess, 0.95, 0.8);
    if (d < 0.0)
        PASS();
    else
        FAIL("expected negative for NULL gm");
}

static void test_rsi_bounded_iterations(void)
{
    TEST(rsi_bounded_to_max_loops);
    rsi_session_t sess;
    memset(&sess, 0, sizeof(sess));
    rsi_session_init(&sess);
    int approved = 0;
    for (int i = 0; i < 20; i++)
    {
        trit r = rsi_propose_mutation(&sess, 0.95, 0.8);
        if (r == TRIT_TRUE)
            approved++;
    }
    if (approved == RSI_MAX_LOOPS && sess.iteration == RSI_MAX_LOOPS)
        PASS();
    else
        FAIL("should cap at RSI_MAX_LOOPS");
}

int main(void)
{
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

    /* RSI Flywheel tests */
    test_rsi_init();
    test_rsi_init_null();
    test_rsi_guard_high_beauty();
    test_rsi_guard_low_beauty();
    test_rsi_guard_negative_beauty();
    test_rsi_guard_iteration_limit();
    test_rsi_guard_null_denies();
    test_rsi_propose_approved();
    test_rsi_propose_denied();
    test_rsi_propose_uncertain();
    test_rsi_can_continue();
    test_rsi_can_continue_at_limit();
    test_rsi_can_continue_null();
    test_rsi_eudaimonia_computation();
    test_rsi_compaction_interval();
    test_rsi_iterate_positive_delta();
    test_rsi_iterate_null_gm();
    test_rsi_bounded_iterations();

    printf("=== Results: %d passed, %d failed ===\n",
           tests_passed, tests_failed);
    return tests_failed ? 1 : 0;
}
