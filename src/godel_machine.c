/**
 * @file godel_machine.c
 * @brief T-045: Gödel Machine Core Engine
 *
 * Implements the 6 proof manipulation instructions as a C API,
 * based on Schmidhuber 2003 + DGM (Darwin Gödel Machine) patterns.
 *
 * State: s(t) = {src/ *.c, tests/ *, proof/ *.thy, Makefile, test_results}
 * Utility: u(s,Env) = Σ(test_pass × proof_verified × trit_coverage)
 * Instructions:
 *   1. godel_get_axiom(n)        — retrieve nth axiom from .thy files
 *   2. godel_apply_rule(k,m,n)   — apply inference rule k to theorems m,n
 *   3. godel_delete_theorem(m)    — remove obsolete theorem
 *   4. godel_set_switchprog(m,n) — configure code segment for replacement
 *   5. godel_check()             — verify theorem matches improvement target
 *   6. godel_state2theorem(m,n)  — encode runtime state as new theorem
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>

/* VULN-12 fix: offset so axiom IDs never overlap theorem IDs */
#define GODEL_AXIOM_OFFSET 10000

/* ── Configuration ── */
#define GODEL_MAX_AXIOMS 256
#define GODEL_MAX_THEOREMS 512
#define GODEL_MAX_RULES 64
#define GODEL_MAX_SWITCHPROGS 32
#define GODEL_MAX_NAME_LEN 128
#define GODEL_MAX_CONTENT_LEN 1024

/* ── Axiom Types ── */
typedef enum
{
    GODEL_AXIOM_HARDWARE = 0,    /* trit state transitions */
    GODEL_AXIOM_REWARD = 1,      /* test_pass, proof_verified, etc. */
    GODEL_AXIOM_ENVIRONMENT = 2, /* build system model */
    GODEL_AXIOM_UTILITY = 3,     /* utility definition */
    GODEL_AXIOM_STATE = 4,       /* initial state encoding */
} godel_axiom_type_t;

/* ── Inference Rules ── */
typedef enum
{
    GODEL_RULE_MODUS_PONENS = 0, /* p, p→q ⊢ q */
    GODEL_RULE_CONJUNCTION = 1,  /* p, q ⊢ p∧q */
    GODEL_RULE_UNIVERSAL = 2,    /* φ(a) for arbitrary a ⊢ ∀x.φ(x) */
    GODEL_RULE_SUBSTITUTION = 3, /* ∀x.φ(x) ⊢ φ(t) */
    GODEL_RULE_INDUCTION = 4,    /* φ(0), φ(n)→φ(n+1) ⊢ ∀n.φ(n) */
    GODEL_RULE_TRIT_EVAL = 5,    /* evaluate trit expression */
} godel_rule_t;

/* ── Theorem ── */
typedef struct
{
    int id;
    char name[GODEL_MAX_NAME_LEN];
    char content[GODEL_MAX_CONTENT_LEN];
    godel_axiom_type_t type;
    int derived_from[2]; /* parent theorem IDs, -1 if axiom */
    godel_rule_t derived_rule;
    trit verified; /* +1=verified, 0=unknown, -1=disproved */
    trit active;   /* +1=active, 0=suspended, -1=deleted */
} godel_theorem_t;

/* ── Switchprog (code replacement spec) ── */
typedef struct
{
    int id;
    char filepath[GODEL_MAX_NAME_LEN];
    char old_content[GODEL_MAX_CONTENT_LEN];
    char new_content[GODEL_MAX_CONTENT_LEN];
    int theorem_id;          /* theorem justifying this replacement */
    trit applied;            /* +1=applied, 0=pending, -1=reverted */
    double expected_delta_u; /* expected utility improvement */
} godel_switchprog_t;

/* ── Gödel Machine State ── */
typedef struct
{
    godel_theorem_t axioms[GODEL_MAX_AXIOMS];
    int n_axioms;
    godel_theorem_t theorems[GODEL_MAX_THEOREMS];
    int n_theorems;
    godel_switchprog_t switchprogs[GODEL_MAX_SWITCHPROGS];
    int n_switchprogs;

    /* Runtime metrics */
    int tests_total;
    int tests_passing;
    int proofs_total;
    int proofs_verified;
    int trit_functions;
    int total_functions;
    int binary_reversions;

    /* Utility tracking */
    double current_utility;
    double previous_utility;
    double delta_utility;

    /* BIOPS scheduler state */
    double search_fraction; /* fraction of build time for search */
    int search_budget_ms;
    int search_elapsed_ms;
    int generation;

    trit initialized; /* +1=ready, 0=partial, -1=uninit */
} godel_machine_t;

/* ── API Implementation ── */

int godel_init(godel_machine_t *gm)
{
    if (!gm)
        return -1;
    memset(gm, 0, sizeof(*gm));
    gm->search_fraction = 0.1; /* 10% of build time for proof search */
    gm->initialized = TRIT_TRUE;

    /* Install foundational axioms */

    /* A1: Trit state axiom — values are {-1, 0, +1} */
    godel_theorem_t *a = &gm->axioms[0];
    a->id = 0;
    a->type = GODEL_AXIOM_HARDWARE;
    snprintf(a->name, sizeof(a->name), "trit_range");
    snprintf(a->content, sizeof(a->content),
             "forall t:trit. t = -1 \\/ t = 0 \\/ t = 1");
    a->derived_from[0] = a->derived_from[1] = -1;
    a->verified = TRIT_TRUE;
    a->active = TRIT_TRUE;

    /* A2: Kleene AND semantics */
    a = &gm->axioms[1];
    a->id = 1;
    a->type = GODEL_AXIOM_HARDWARE;
    snprintf(a->name, sizeof(a->name), "kleene_and");
    snprintf(a->content, sizeof(a->content),
             "forall a b:trit. trit_and(a,b) = min(a,b)");
    a->derived_from[0] = a->derived_from[1] = -1;
    a->verified = TRIT_TRUE;
    a->active = TRIT_TRUE;

    /* A3: Reward axiom — test pass = +1 */
    a = &gm->axioms[2];
    a->id = 2;
    a->type = GODEL_AXIOM_REWARD;
    snprintf(a->name, sizeof(a->name), "reward_test_pass");
    snprintf(a->content, sizeof(a->content),
             "forall t:test. pass(t) -> reward(t) = +1");
    a->derived_from[0] = a->derived_from[1] = -1;
    a->verified = TRIT_TRUE;
    a->active = TRIT_TRUE;

    /* A4: Environment axiom — build is deterministic */
    a = &gm->axioms[3];
    a->id = 3;
    a->type = GODEL_AXIOM_ENVIRONMENT;
    snprintf(a->name, sizeof(a->name), "env_deterministic");
    snprintf(a->content, sizeof(a->content),
             "forall s:state. build(s) = build(s)  [deterministic]");
    a->derived_from[0] = a->derived_from[1] = -1;
    a->verified = TRIT_TRUE;
    a->active = TRIT_TRUE;

    /* A5: Utility definition */
    a = &gm->axioms[4];
    a->id = 4;
    a->type = GODEL_AXIOM_UTILITY;
    snprintf(a->name, sizeof(a->name), "utility_def");
    snprintf(a->content, sizeof(a->content),
             "u(s,E) = (pass/total) * (proofs_ok/proofs) * (trit/funcs) * (1 - reversions/funcs)");
    a->derived_from[0] = a->derived_from[1] = -1;
    a->verified = TRIT_TRUE;
    a->active = TRIT_TRUE;

    /* A6: Initial state encoding */
    a = &gm->axioms[5];
    a->id = 5;
    a->type = GODEL_AXIOM_STATE;
    snprintf(a->name, sizeof(a->name), "initial_state");
    snprintf(a->content, sizeof(a->content),
             "s(1) = {tests:1792, suites:34, proofs:8, reversions:0}");
    a->derived_from[0] = a->derived_from[1] = -1;
    a->verified = TRIT_TRUE;
    a->active = TRIT_TRUE;

    gm->n_axioms = 6;
    return 0;
}

/* Instruction 1: Get axiom */
const godel_theorem_t *godel_get_axiom(const godel_machine_t *gm, int n)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return NULL;
    if (n < 0 || n >= gm->n_axioms)
        return NULL;
    return &gm->axioms[n];
}

/* Instruction 2: Apply inference rule */
int godel_apply_rule(godel_machine_t *gm, godel_rule_t rule,
                     int theorem_m, int theorem_n)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return -1;
    if (gm->n_theorems >= GODEL_MAX_THEOREMS)
        return -1;

    /* Validate input theorems — VULN-12 fix: check theorem space first,
     * then axiom space with explicit GODEL_AXIOM_OFFSET separation.
     * Axiom IDs are theorem_m >= GODEL_AXIOM_OFFSET. */
    godel_theorem_t *tm = NULL, *tn = NULL;
    if (theorem_m >= GODEL_AXIOM_OFFSET) {
        int axiom_idx = theorem_m - GODEL_AXIOM_OFFSET;
        if (axiom_idx >= 0 && axiom_idx < gm->n_axioms)
            tm = &gm->axioms[axiom_idx];
    } else if (theorem_m >= 0 && theorem_m < gm->n_theorems) {
        tm = &gm->theorems[theorem_m];
    }
    if (theorem_n >= GODEL_AXIOM_OFFSET) {
        int axiom_idx = theorem_n - GODEL_AXIOM_OFFSET;
        if (axiom_idx >= 0 && axiom_idx < gm->n_axioms)
            tn = &gm->axioms[axiom_idx];
    } else if (theorem_n >= 0 && theorem_n < gm->n_theorems) {
        tn = &gm->theorems[theorem_n];
    }

    godel_theorem_t *new_thm = &gm->theorems[gm->n_theorems];
    new_thm->id = gm->n_theorems;
    new_thm->derived_from[0] = theorem_m;
    new_thm->derived_from[1] = theorem_n;
    new_thm->derived_rule = rule;
    new_thm->active = TRIT_TRUE;
    new_thm->verified = TRIT_UNKNOWN;

    switch (rule)
    {
    case GODEL_RULE_MODUS_PONENS:
        if (!tm || !tn)
            return -1;
        snprintf(new_thm->name, sizeof(new_thm->name),
                 "mp_%d_%d", theorem_m, theorem_n);
        snprintf(new_thm->content, sizeof(new_thm->content),
                 "modus_ponens(%s, %s)", tm->name, tn->name);
        new_thm->verified = trit_and(tm->verified, tn->verified);
        break;

    case GODEL_RULE_CONJUNCTION:
        if (!tm || !tn)
            return -1;
        snprintf(new_thm->name, sizeof(new_thm->name),
                 "conj_%d_%d", theorem_m, theorem_n);
        snprintf(new_thm->content, sizeof(new_thm->content),
                 "(%s) /\\ (%s)", tm->content, tn->content);
        new_thm->verified = trit_and(tm->verified, tn->verified);
        break;

    case GODEL_RULE_TRIT_EVAL:
        /* Special: evaluate a trit expression from runtime state */
        snprintf(new_thm->name, sizeof(new_thm->name),
                 "trit_eval_%d", gm->n_theorems);
        snprintf(new_thm->content, sizeof(new_thm->content),
                 "trit_eval(runtime_state) => pending_verification");
        /* VULN-13 fix: TRIT_EVAL no longer auto-verifies — requires
         * separate verification step (godel_check or manual audit) */
        new_thm->verified = TRIT_UNKNOWN;
        break;

    default:
        snprintf(new_thm->name, sizeof(new_thm->name),
                 "derived_%d", gm->n_theorems);
        snprintf(new_thm->content, sizeof(new_thm->content),
                 "rule_%d(%s)", rule, tm ? tm->name : "?");
        break;
    }

    gm->n_theorems++;
    return new_thm->id;
}

/* Instruction 3: Delete theorem */
int godel_delete_theorem(godel_machine_t *gm, int theorem_id)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return -1;
    if (theorem_id < 0 || theorem_id >= gm->n_theorems)
        return -1;
    gm->theorems[theorem_id].active = TRIT_FALSE;
    return 0;
}

/* Instruction 4: Set switchprog */
int godel_set_switchprog(godel_machine_t *gm, const char *filepath,
                         const char *old_content, const char *new_content,
                         int theorem_id, double expected_delta_u)
{
    if (!gm || gm->initialized != TRIT_TRUE || !filepath)
        return -1;
    if (gm->n_switchprogs >= GODEL_MAX_SWITCHPROGS)
        return -1;

    godel_switchprog_t *sp = &gm->switchprogs[gm->n_switchprogs];
    sp->id = gm->n_switchprogs;
    snprintf(sp->filepath, sizeof(sp->filepath), "%s", filepath);
    if (old_content)
        snprintf(sp->old_content, sizeof(sp->old_content), "%s", old_content);
    if (new_content) {
        /* VULN-14 fix: detect truncation and return error */
        int needed = snprintf(sp->new_content, sizeof(sp->new_content), "%s", new_content);
        if (needed >= (int)sizeof(sp->new_content))
            return -1;  /* content too long, refuse to truncate silently */
    }
    sp->theorem_id = theorem_id;
    sp->applied = TRIT_UNKNOWN; /* pending */
    sp->expected_delta_u = expected_delta_u;

    gm->n_switchprogs++;
    return sp->id;
}

/* Instruction 5: Check */
int godel_check(const godel_machine_t *gm)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return 0;

    /* Verify latest theorem matches self-improvement criterion:
     * Δu > cost(rewrite) / normalization */
    if (gm->n_theorems == 0)
        return 0;

    const godel_theorem_t *latest = &gm->theorems[gm->n_theorems - 1];
    if (latest->active != TRIT_TRUE || latest->verified != TRIT_TRUE)
        return 0;

    /* Check that utility improved — ternary: +1=improving, 0=neutral, -1=regressing */
    if (gm->delta_utility > 0)
        return 1;
    if (gm->delta_utility < 0)
        return -1;
    return 0;
}

/* Instruction 6: State to theorem */
int godel_state2theorem(godel_machine_t *gm)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return -1;
    if (gm->n_theorems >= GODEL_MAX_THEOREMS)
        return -1;

    godel_theorem_t *thm = &gm->theorems[gm->n_theorems];
    thm->id = gm->n_theorems;
    thm->type = GODEL_AXIOM_STATE;
    snprintf(thm->name, sizeof(thm->name),
             "state_gen%d", gm->generation);
    snprintf(thm->content, sizeof(thm->content),
             "state(tests=%d/%d, proofs=%d/%d, trit=%d/%d, rev=%d, u=%.6f)",
             gm->tests_passing, gm->tests_total,
             gm->proofs_verified, gm->proofs_total,
             gm->trit_functions, gm->total_functions,
             gm->binary_reversions, gm->current_utility);
    thm->derived_from[0] = thm->derived_from[1] = -1;
    thm->derived_rule = GODEL_RULE_TRIT_EVAL;
    thm->verified = TRIT_TRUE;
    thm->active = TRIT_TRUE;

    gm->n_theorems++;
    return thm->id;
}

/* ── Utility computation ── */

double godel_compute_utility(godel_machine_t *gm)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return 0.0;

    double u_tests = (gm->tests_total > 0) ? (double)gm->tests_passing / gm->tests_total : 0.0;
    double u_proofs = (gm->proofs_total > 0) ? (double)gm->proofs_verified / gm->proofs_total : 0.0;
    double u_trit = (gm->total_functions > 0) ? (double)gm->trit_functions / gm->total_functions : 0.0;
    double u_revert = (gm->total_functions > 0) ? 1.0 - (double)gm->binary_reversions / gm->total_functions : 1.0;

    gm->previous_utility = gm->current_utility;
    gm->current_utility = u_tests * u_proofs * u_trit * u_revert;
    gm->delta_utility = gm->current_utility - gm->previous_utility;

    return gm->current_utility;
}

/* ── Update runtime metrics from test results ── */

int godel_update_metrics(godel_machine_t *gm,
                         int tests_pass, int tests_total,
                         int proofs_ok, int proofs_total,
                         int trit_funcs, int total_funcs,
                         int binary_reverts)
{
    if (!gm || gm->initialized != TRIT_TRUE)
        return -1;
    gm->tests_passing = tests_pass;
    gm->tests_total = tests_total;
    gm->proofs_verified = proofs_ok;
    gm->proofs_total = proofs_total;
    gm->trit_functions = trit_funcs;
    gm->total_functions = total_funcs;
    gm->binary_reversions = binary_reverts;
    return 0;
}

/* ══════════════════════════════════════════════════════════════════════
 *  RSI FLYWHEEL — Bounded Recursive Self-Improvement
 *
 *  Per RSI_OPTIMIZATION_INSTRUCTIONS.md:
 *  - Cap: RSI_MAX_LOOPS per session (prevents runaway)
 *  - Trit guards: -1 deny coercive, 0 query human, +1 proceed
 *  - Beauty/curiosity thresholds gate each iteration
 *  - Session compaction every 5 iterations
 * ══════════════════════════════════════════════════════════════════════ */

#define RSI_MAX_LOOPS 10
#define RSI_BEAUTY_THRESHOLD 0.9
#define RSI_CURIOSITY_MIN 0.5
#define RSI_COMPACTION_INTERVAL 5

/* VULN-10 fix: monotonic generation counter survives reinit */
static int rsi_global_generation = 0;
static int rsi_total_iterations = 0;

typedef struct
{
    int iteration;
    int generation;          /* VULN-10: monotonic generation ID */
    trit access_guard;      /* -1=deny, 0=query, +1=proceed */
    double beauty_score;    /* Symmetry/harmony metric */
    double curiosity_level; /* Exploration drive */
    double eudaimonia;      /* Combined flourishing metric */
    int mutations_applied;
    int mutations_rejected;
    int human_queries;       /* Times we deferred to human this session */
    int total_human_queries; /* VULN-11: cumulative across compactions */
} rsi_session_t;

/* Evaluate trit guard for an RSI action */
trit rsi_trit_guard(const rsi_session_t *session, double proposed_beauty)
{
    if (!session)
        return TRIT_FALSE;

    /* -1: Deny if coercive (beauty below threshold or iteration exceeded) */
    if (session->iteration >= RSI_MAX_LOOPS)
        return TRIT_FALSE;
    if (proposed_beauty < 0.0)
        return TRIT_FALSE;

    /* 0: Query human if uncertain (beauty in gray zone) */
    if (proposed_beauty < RSI_BEAUTY_THRESHOLD)
        return TRIT_UNKNOWN;

    /* +1: Proceed if beauty-symmetric and curiosity alive */
    if (proposed_beauty >= RSI_BEAUTY_THRESHOLD &&
        session->curiosity_level >= RSI_CURIOSITY_MIN)
        return TRIT_TRUE;

    return TRIT_UNKNOWN; /* Default: uncertain → query */
}

/* Initialize an RSI session */
int rsi_session_init(rsi_session_t *session)
{
    if (!session)
        return -1;
    /* VULN-10 fix: increment global generation, don't reset total iterations */
    rsi_global_generation++;
    int saved_total_queries = session->total_human_queries;
    memset(session, 0, sizeof(*session));
    session->generation = rsi_global_generation;
    session->total_human_queries = saved_total_queries; /* VULN-11: preserve */
    session->access_guard = TRIT_TRUE;
    session->beauty_score = 1.0;
    session->curiosity_level = 1.0;
    session->eudaimonia = 1.0;
    return 0;
}

/* Propose a mutation — returns trit guard decision */
trit rsi_propose_mutation(rsi_session_t *session,
                          double proposed_beauty,
                          double proposed_curiosity)
{
    if (!session)
        return TRIT_FALSE;

    trit guard = rsi_trit_guard(session, proposed_beauty);

    if (guard == TRIT_FALSE)
    {
        session->mutations_rejected++;
        return TRIT_FALSE;
    }
    if (guard == TRIT_UNKNOWN)
    {
        session->human_queries++;
        return TRIT_UNKNOWN;
    }

    /* Guard approved — apply mutation */
    session->iteration++;
    rsi_total_iterations++;  /* VULN-10: global counter */
    session->mutations_applied++;
    session->beauty_score = proposed_beauty;
    session->curiosity_level = proposed_curiosity;
    session->eudaimonia = proposed_beauty * proposed_curiosity;

    /* Session compaction check */
    if (session->iteration % RSI_COMPACTION_INTERVAL == 0)
    {
        /* Compact session state — VULN-11 fix: preserve audit trail */
        session->total_human_queries += session->human_queries;
        session->human_queries = 0;  /* reset per-interval counter only */
    }

    return TRIT_TRUE;
}

/* Run one RSI iteration — returns utility delta */
double rsi_iterate(godel_machine_t *gm, rsi_session_t *session,
                   double proposed_beauty, double proposed_curiosity)
{
    if (!gm || !session)
        return -1.0;

    trit decision = rsi_propose_mutation(session, proposed_beauty,
                                         proposed_curiosity);
    if (decision != TRIT_TRUE)
        return 0.0; /* No mutation applied */

    /* Recalculate utility after mutation */
    double old_utility = gm->current_utility;
    double new_utility = godel_compute_utility(gm);
    double delta = new_utility - old_utility;

    /* Reject if utility decreased */
    if (delta < 0.0)
    {
        session->mutations_rejected++;
        session->mutations_applied--;
        return delta;
    }

    return delta;
}

/* Check if session can continue */
int rsi_can_continue(const rsi_session_t *session)
{
    if (!session)
        return 0;
    /* VULN-10 fix: check TOTAL iterations across all generations,
     * not just per-session iteration */
    return (rsi_total_iterations < RSI_MAX_LOOPS * 10 &&
            session->iteration < RSI_MAX_LOOPS &&
            session->access_guard != TRIT_FALSE);
}

/* Get session summary for logging */
void rsi_session_summary(const rsi_session_t *session)
{
    if (!session)
        return;
    printf("RSI Session: iter=%d/%d applied=%d rejected=%d "
           "beauty=%.3f curiosity=%.3f eudaimonia=%.3f\n",
           session->iteration, RSI_MAX_LOOPS,
           session->mutations_applied, session->mutations_rejected,
           session->beauty_score, session->curiosity_level,
           session->eudaimonia);
}
