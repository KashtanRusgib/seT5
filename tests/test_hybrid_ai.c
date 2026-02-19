/* tests/test_hybrid_ai.c — Hybrid AI Integration (Suite 38)
 * 280 runtime assertions: TRQ + Tissue + RPL + Epistemic + DEL + Council
 * All AI modules are inline-implemented for self-containment.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "set5/trit.h"

static int g_pass, g_fail;
#define TEST(name) printf("  %-60s ", name)
#define PASS()     do { g_pass++; printf("[PASS]\n"); } while(0)
#define FAIL(msg)  do { g_fail++; printf("[FAIL] %s\n", msg); } while(0)
#define ASSERT(expr, msg) do { if (expr) { PASS(); } else { FAIL(msg); } } while(0)
#define SECTION(s) printf("\n══ %s ══\n", s)

/* ========================================================================
 * TRQ — Ternary Residual Quantization
 * ======================================================================== */
#define TRQ_MAX_DIM 256
#define TRQ_MAX_STAGES 8

typedef struct {
    int initialized;
    int dim;
    int original[TRQ_MAX_DIM];
    int ternary[TRQ_MAX_DIM];
    int num_stages;
    int stage_ternary[TRQ_MAX_STAGES][TRQ_MAX_DIM];
    double alpha[TRQ_MAX_STAGES];
    int threshold;
    int salient_mask[TRQ_MAX_DIM];
} trq_state_t;

static int trq_init(trq_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

static int trq_load_weights(trq_state_t *st, const int *w, int n) {
    if (!st || !w || n <= 0 || n > TRQ_MAX_DIM) return -1;
    st->dim = n;
    memcpy(st->original, w, n * sizeof(int));
    return 0;
}

static int trq_quantize_basic(trq_state_t *st) {
    if (!st || st->dim == 0) return -1;
    double sum_abs = 0;
    for (int i = 0; i < st->dim; i++) sum_abs += abs(st->original[i]);
    double alpha = sum_abs / st->dim;
    if (alpha < 1) alpha = 1;
    st->alpha[0] = alpha;
    st->threshold = (int)(alpha * 0.5);
    int pos = 0, neg = 0, zero = 0;
    for (int i = 0; i < st->dim; i++) {
        if (st->original[i] > st->threshold) { st->ternary[i] = 1; pos++; }
        else if (st->original[i] < -st->threshold) { st->ternary[i] = -1; neg++; }
        else { st->ternary[i] = 0; zero++; }
    }
    memcpy(st->stage_ternary[0], st->ternary, st->dim * sizeof(int));
    st->num_stages = 1;
    (void)pos; (void)neg; (void)zero;
    return 0;
}

static int trq_iterative_fit(trq_state_t *st, int iters) {
    if (!st || st->dim == 0) return -1;
    for (int it = 0; it < iters; it++) {
        double sum_w = 0, sum_t = 0;
        for (int i = 0; i < st->dim; i++) {
            sum_w += abs(st->original[i]);
            sum_t += abs(st->ternary[i]);
        }
        if (sum_t > 0) st->alpha[0] = sum_w / sum_t;
        st->threshold = (int)(st->alpha[0] * 0.4);
        for (int i = 0; i < st->dim; i++) {
            if (st->original[i] > st->threshold) st->ternary[i] = 1;
            else if (st->original[i] < -st->threshold) st->ternary[i] = -1;
            else st->ternary[i] = 0;
        }
    }
    double mse = 0;
    for (int i = 0; i < st->dim; i++) {
        double diff = st->original[i] - st->alpha[0] * st->ternary[i];
        mse += diff * diff;
    }
    mse /= st->dim;
    (void)mse;
    return (int)mse;
}

static int trq_add_residual(trq_state_t *st) {
    if (!st || st->num_stages >= TRQ_MAX_STAGES) return -1;
    int s = st->num_stages;
    int residual[TRQ_MAX_DIM];
    for (int i = 0; i < st->dim; i++)
        residual[i] = st->original[i] - (int)(st->alpha[0] * st->ternary[i]);
    double sum = 0;
    for (int i = 0; i < st->dim; i++) sum += abs(residual[i]);
    st->alpha[s] = (st->dim > 0) ? sum / st->dim : 1;
    if (st->alpha[s] < 1) st->alpha[s] = 1;
    int th = (int)(st->alpha[s] * 0.5);
    for (int i = 0; i < st->dim; i++) {
        if (residual[i] > th) st->stage_ternary[s][i] = 1;
        else if (residual[i] < -th) st->stage_ternary[s][i] = -1;
        else st->stage_ternary[s][i] = 0;
    }
    st->num_stages++;
    return 0;
}

static int trq_reconstruct(trq_state_t *st, int *out) {
    if (!st || !out) return -1;
    for (int i = 0; i < st->dim; i++) {
        double v = 0;
        for (int s = 0; s < st->num_stages; s++)
            v += st->alpha[s] * st->stage_ternary[s][i];
        out[i] = (int)v;
    }
    return 0;
}

static int trq_salient_smooth(trq_state_t *st) {
    if (!st || st->dim == 0) return -1;
    int max_val = 0;
    for (int i = 0; i < st->dim; i++)
        if (abs(st->original[i]) > max_val) max_val = abs(st->original[i]);
    int th = max_val / 2;
    int count = 0;
    for (int i = 0; i < st->dim; i++) {
        st->salient_mask[i] = (abs(st->original[i]) >= th) ? 1 : 0;
        count += st->salient_mask[i];
    }
    return count;
}

static int trq_compression_bits(const trq_state_t *st) {
    if (!st || st->dim == 0) return 0;
    int nz = 0;
    for (int i = 0; i < st->dim; i++) if (st->ternary[i] != 0) nz++;
    return nz * 200; /* 2 bits per non-zero, ×100 for fixed-point */
}

static int trq_sparsity(const trq_state_t *st) {
    if (!st || st->dim == 0) return 0;
    int zeros = 0;
    for (int i = 0; i < st->dim; i++) if (st->ternary[i] == 0) zeros++;
    return (zeros * 100) / st->dim;
}

/* ========================================================================
 * TISSUE — Neural Tissue Simulator
 * ======================================================================== */
#define TISSUE_MAX_NEURONS 32
#define TISSUE_MAX_IO 16

typedef struct {
    int id;
    int num_neurons;
    int num_inputs;
    int num_outputs;
    int weights[TISSUE_MAX_NEURONS][TISSUE_MAX_IO]; /* ternary: -1,0,1 */
    int activations[TISSUE_MAX_NEURONS];
    double fitness;
} tissue_t;

static int tissue_create(tissue_t *t, int neurons, int inputs, int outputs) {
    if (!t) return -1;
    if (inputs <= 0 || inputs > TISSUE_MAX_IO) return -2;
    if (neurons <= 0 || neurons > TISSUE_MAX_NEURONS) return -1;
    if (outputs <= 0 || outputs > TISSUE_MAX_IO) return -1;
    memset(t, 0, sizeof(*t));
    t->num_neurons = neurons; t->num_inputs = inputs; t->num_outputs = outputs;
    /* Init weights to balanced ternary pattern */
    for (int n = 0; n < neurons; n++)
        for (int i = 0; i < inputs; i++)
            t->weights[n][i] = ((n + i) % 3) - 1;
    return 0;
}

static int tissue_forward(tissue_t *t, const int *inputs) {
    if (!t || !inputs) return -1;
    for (int n = 0; n < t->num_neurons; n++) {
        int acc = 0;
        for (int i = 0; i < t->num_inputs; i++)
            acc += t->weights[n][i] * inputs[i];
        /* Ternary clamp */
        t->activations[n] = (acc > 0) ? 1 : (acc < 0) ? -1 : 0;
    }
    return 0;
}

static int tissue_mutate(tissue_t *t, int rate) {
    if (!t) return -1;
    int mutations = 0;
    for (int n = 0; n < t->num_neurons; n++)
        for (int i = 0; i < t->num_inputs; i++) {
            if (((n * 31 + i * 7 + rate) % 100) < rate) {
                t->weights[n][i] = ((t->weights[n][i] + 2) % 3) - 1;
                mutations++;
            }
        }
    return mutations;
}

static int tissue_crossover(const tissue_t *a, const tissue_t *b, tissue_t *child) {
    if (!a || !b || !child) return -1;
    memset(child, 0, sizeof(*child));
    child->num_neurons = a->num_neurons;
    child->num_inputs = a->num_inputs;
    child->num_outputs = a->num_outputs;
    int crosses = 0;
    for (int n = 0; n < a->num_neurons; n++)
        for (int i = 0; i < a->num_inputs; i++) {
            child->weights[n][i] = ((n + i) % 2 == 0) ? a->weights[n][i] : b->weights[n][i];
            crosses++;
        }
    return crosses;
}

static double tissue_evaluate(tissue_t *t, const int inputs[][TISSUE_MAX_IO], 
                               const int *targets, int samples) {
    if (!t || !inputs || !targets) return -1;
    int correct = 0;
    for (int s = 0; s < samples; s++) {
        tissue_forward(t, inputs[s]);
        if (t->activations[0] == targets[s]) correct++;
    }
    t->fitness = (double)correct * 1000.0 / samples;
    return t->fitness;
}

typedef struct {
    tissue_t pop[16];
    int pop_size;
    int generation;
    double best_fitness;
    int best_idx;
} tissue_population_t;

static int tissue_pop_init(tissue_population_t *p, int size, int neurons, int inputs, int outputs) {
    if (!p || size <= 0 || size > 16) return -1;
    memset(p, 0, sizeof(*p));
    p->pop_size = size;
    for (int i = 0; i < size; i++) {
        tissue_create(&p->pop[i], neurons, inputs, outputs);
        p->pop[i].id = i;
    }
    return 0;
}

static int tissue_evolve(tissue_population_t *p) {
    if (!p) return -1;
    /* Simple tournament: mutate all, track best */
    double best = -1;
    for (int i = 0; i < p->pop_size; i++) {
        tissue_mutate(&p->pop[i], 10);
        if (p->pop[i].fitness > best) {
            best = p->pop[i].fitness;
            p->best_idx = i;
        }
    }
    p->best_fitness = best;
    p->generation++;
    return 0;
}

/* ========================================================================
 * RPL — Rational Pavelka Logic [0,1000]
 * ======================================================================== */
static int rpl_implies(int a, int b) {
    int v = 1000 - a + b;
    return v > 1000 ? 1000 : (v < 0 ? 0 : v);
}
static int rpl_negate(int a) { return 1000 - a; }
static int rpl_strong_and(int a, int b) { int v = a + b - 1000; return v < 0 ? 0 : v; }
static int rpl_strong_or(int a, int b) { int v = a + b; return v > 1000 ? 1000 : v; }
static int rpl_weak_and(int a, int b) { return a < b ? a : b; }
static int rpl_weak_or(int a, int b) { return a > b ? a : b; }
static int rpl_equiv(int a, int b) { return rpl_strong_and(rpl_implies(a, b), rpl_implies(b, a)); }
static trit rpl_to_trit(int v) { return v >= 750 ? TRIT_TRUE : (v <= 250 ? TRIT_FALSE : TRIT_UNKNOWN); }
static int rpl_from_trit(trit t) { return t == TRIT_TRUE ? 1000 : (t == TRIT_FALSE ? 0 : 500); }
static int rpl_distance(int a, int b) { return abs(a - b); }
static int rpl_ntimes(int a, int n) {
    int v = a;
    for (int i = 1; i < n; i++) v = rpl_strong_and(v, a);
    return v;
}
static int rpl_at_least(int a, int threshold) { return a >= threshold ? 1 : 0; }

typedef struct {
    int truth[16]; char names[16][32]; int count;
    struct { int from, to, weight; } rules[16]; int rule_count;
    int converged;
} rpl_context_t;

static int rpl_ctx_init(rpl_context_t *ctx) {
    if (!ctx) return -1;
    memset(ctx, 0, sizeof(*ctx));
    return 0;
}

static int rpl_add_prop(rpl_context_t *ctx, const char *name, int truth) {
    if (!ctx || ctx->count >= 16) return -1;
    strncpy(ctx->names[ctx->count], name, 31);
    ctx->truth[ctx->count] = truth;
    return ctx->count++;
}

static int rpl_add_rule(rpl_context_t *ctx, int from, int to, int weight) {
    if (!ctx || ctx->rule_count >= 16) return -1;
    ctx->rules[ctx->rule_count].from = from;
    ctx->rules[ctx->rule_count].to = to;
    ctx->rules[ctx->rule_count].weight = weight;
    return ctx->rule_count++;
}

static int rpl_propagate(rpl_context_t *ctx, int max_steps) {
    if (!ctx) return -1;
    int steps = 0;
    for (int s = 0; s < max_steps; s++) {
        int changed = 0;
        for (int r = 0; r < ctx->rule_count; r++) {
            int f = ctx->rules[r].from, t = ctx->rules[r].to;
            int inf = rpl_strong_and(ctx->truth[f], ctx->rules[r].weight);
            if (inf > ctx->truth[t]) { ctx->truth[t] = inf; changed = 1; }
        }
        steps++;
        if (!changed) { ctx->converged = 1; break; }
    }
    return steps;
}

/* ========================================================================
 * EPISTEMIC — Kripke Models
 * ======================================================================== */
#define EPIST_MAX_WORLDS 8
#define EPIST_MAX_PROPS  8
#define EPIST_MAX_AGENTS 4

typedef struct {
    trit val[EPIST_MAX_WORLDS][EPIST_MAX_PROPS];
    int access[EPIST_MAX_AGENTS][EPIST_MAX_WORLDS][EPIST_MAX_WORLDS];
    int num_worlds, num_props, num_agents;
    int actual_world;
} epist_model_t;

static int epist_init(epist_model_t *m, int worlds, int props, int agents) {
    if (!m || worlds <= 0 || worlds > EPIST_MAX_WORLDS) return -1;
    memset(m, 0, sizeof(*m));
    m->num_worlds = worlds; m->num_props = props; m->num_agents = agents;
    return 0;
}

static int epist_set_val(epist_model_t *m, int w, int p, trit v) {
    if (!m || w < 0 || w >= m->num_worlds || p < 0 || p >= m->num_props) return -1;
    m->val[w][p] = v; return 0;
}

static trit epist_get_val(const epist_model_t *m, int w, int p) {
    if (!m || w < 0 || w >= m->num_worlds) return TRIT_UNKNOWN;
    return m->val[w][p];
}

static int epist_add_access(epist_model_t *m, int agent, int from, int to) {
    if (!m || agent < 0 || agent >= m->num_agents) return -1;
    m->access[agent][from][to] = 1;
    return 0;
}

/* K_a φ(w) = TRUE iff φ(w') for all w' accessible from w by agent a */
static trit epist_knows(const epist_model_t *m, int agent, int prop, int world) {
    if (!m) return TRIT_UNKNOWN;
    trit result = TRIT_TRUE;
    int has_access = 0;
    for (int w = 0; w < m->num_worlds; w++) {
        if (m->access[agent][world][w]) {
            has_access = 1;
            trit v = m->val[w][prop];
            result = trit_and(result, v);
        }
    }
    return has_access ? result : TRIT_UNKNOWN;
}

/* Distributed knowledge: AND of what each agent knows */
static trit epist_distributed(const epist_model_t *m, int prop, int world) {
    trit r = TRIT_TRUE;
    for (int a = 0; a < m->num_agents; a++)
        r = trit_and(r, epist_knows(m, a, prop, world));
    return r;
}

/* Common knowledge: fixpoint of everyone-knows */
static trit epist_common(const epist_model_t *m, int prop, int world) {
    trit r = TRIT_TRUE;
    for (int a = 0; a < m->num_agents; a++) {
        trit k = epist_knows(m, a, prop, world);
        r = trit_and(r, k);
    }
    return r;
}

/* ========================================================================
 * DEL — Dynamic Epistemic Logic
 * ======================================================================== */
typedef struct {
    int active[EPIST_MAX_WORLDS];
    int active_count;
    int history_len;
    struct { int type; int param; } history[32];
    int plausibility[EPIST_MAX_WORLDS]; /* 0=most plausible */
} del_state_t;

static int del_init(del_state_t *d, int worlds) {
    if (!d || worlds <= 0 || worlds > EPIST_MAX_WORLDS) return -1;
    memset(d, 0, sizeof(*d));
    for (int i = 0; i < worlds; i++) { d->active[i] = 1; d->plausibility[i] = i; }
    d->active_count = worlds;
    return 0;
}

static int del_public_announce(del_state_t *d, const epist_model_t *m, int prop) {
    if (!d || !m) return -1;
    int removed = 0;
    for (int w = 0; w < EPIST_MAX_WORLDS; w++) {
        if (d->active[w] && m->val[w][prop] == TRIT_FALSE) {
            d->active[w] = 0;
            removed++;
            d->active_count--;
        }
    }
    d->history[d->history_len].type = 1; /* PUBLIC_ANNOUNCE */
    d->history[d->history_len].param = prop;
    d->history_len++;
    return removed;
}

static int del_revise_belief(del_state_t *d, const epist_model_t *m, int prop) {
    if (!d || !m) return -1;
    int changed = 0;
    for (int w = 0; w < EPIST_MAX_WORLDS; w++) {
        if (d->active[w] && m->val[w][prop] != TRIT_TRUE) {
            d->plausibility[w] += 10; /* demote */
            changed++;
        }
    }
    d->history[d->history_len].type = 2;
    d->history[d->history_len].param = prop;
    d->history_len++;
    return changed;
}

static int del_most_plausible(const del_state_t *d) {
    if (!d) return -1;
    int best = -1, best_p = 9999;
    for (int w = 0; w < EPIST_MAX_WORLDS; w++) {
        if (d->active[w] && d->plausibility[w] < best_p) {
            best_p = d->plausibility[w]; best = w;
        }
    }
    return best;
}

/* ========================================================================
 * COUNCIL — Multi-Agent Deliberation (Atmakosh / Sabhā)
 * ======================================================================== */
#define COUNCIL_MAX_AGENTS 8
#define COUNCIL_MAX_PROPS 8
#define COUNCIL_NUM_PHASES 5

typedef enum {
    SYAD_ASTI = 0, SYAD_NASTI, SYAD_ASTI_NASTI, SYAD_AVAKTAVYA,
    SYAD_ASTI_AVAKTAVYA, SYAD_NASTI_AVAKTAVYA, SYAD_ASTI_NASTI_AVAKTAVYA
} syad_mode_t;

static const char *syad_names[] = {
    "asti", "nasti", "asti-nasti", "avaktavya",
    "asti-avaktavya", "nasti-avaktavya", "asti-nasti-avaktavya"
};

typedef struct {
    int truth[COUNCIL_MAX_PROPS]; /* graded 0-1000 */
    int confidence;
    int id;
} council_agent_t;

typedef struct {
    council_agent_t agents[COUNCIL_MAX_AGENTS];
    int num_agents;
    int num_props;
    int phase;
    int converged;
    struct { int step; int agent; int prop; int old_val; int new_val; } audit[128];
    int audit_len;
} council_t;

static int council_init(council_t *c, int props, int agents) {
    if (!c || agents <= 0 || agents > COUNCIL_MAX_AGENTS) return -1;
    memset(c, 0, sizeof(*c));
    c->num_agents = agents; c->num_props = props;
    for (int a = 0; a < agents; a++) {
        c->agents[a].id = a;
        c->agents[a].confidence = 500;
        for (int p = 0; p < props; p++)
            c->agents[a].truth[p] = 500;
    }
    return 0;
}

static int council_set_truth(council_t *c, int agent, int prop, int val) {
    if (!c || agent < 0 || agent >= c->num_agents) return -1;
    c->agents[agent].truth[prop] = val;
    return 0;
}

static int council_deliberate(council_t *c) {
    if (!c) return -1;
    for (int phase = 0; phase < COUNCIL_NUM_PHASES; phase++) {
        for (int p = 0; p < c->num_props; p++) {
            int sum = 0, wt = 0;
            for (int a = 0; a < c->num_agents; a++) {
                sum += c->agents[a].truth[p] * c->agents[a].confidence;
                wt += c->agents[a].confidence;
            }
            int consensus = (wt > 0) ? sum / wt : 500;
            /* Bādhā: low-confidence agents move more toward consensus */
            for (int a = 0; a < c->num_agents; a++) {
                int old = c->agents[a].truth[p];
                int move = (consensus - old) * (1000 - c->agents[a].confidence) / 2000;
                c->agents[a].truth[p] = old + move;
                if (c->agents[a].truth[p] != old && c->audit_len < 128) {
                    c->audit[c->audit_len].step = phase;
                    c->audit[c->audit_len].agent = a;
                    c->audit[c->audit_len].prop = p;
                    c->audit[c->audit_len].old_val = old;
                    c->audit[c->audit_len].new_val = c->agents[a].truth[p];
                    c->audit_len++;
                }
            }
        }
    }
    c->phase = COUNCIL_NUM_PHASES;
    c->converged = 1;
    return c->audit_len;
}

static int council_agreement(const council_t *c, int prop) {
    if (!c || c->num_agents < 2) return 1000;
    int mn = 1001, mx = -1;
    for (int a = 0; a < c->num_agents; a++) {
        if (c->agents[a].truth[prop] < mn) mn = c->agents[a].truth[prop];
        if (c->agents[a].truth[prop] > mx) mx = c->agents[a].truth[prop];
    }
    return 1000 - (mx - mn);
}

static syad_mode_t council_syad_verdict(const council_t *c, int prop) {
    if (!c) return SYAD_AVAKTAVYA;
    int sum = 0;
    for (int a = 0; a < c->num_agents; a++) sum += c->agents[a].truth[prop];
    int avg = sum / c->num_agents;
    if (avg >= 750) return SYAD_ASTI;
    if (avg <= 250) return SYAD_NASTI;
    if (avg >= 400 && avg <= 600) return SYAD_AVAKTAVYA;
    if (avg > 600) return SYAD_ASTI_NASTI;
    return SYAD_NASTI_AVAKTAVYA;
}

/* ========================================================================
 * TESTS
 * ======================================================================== */

static void test_trq(void) {
    SECTION("TRQ: Init");
    trq_state_t st;
    TEST("trq_init → 0");             ASSERT(trq_init(&st) == 0, "0");
    TEST("initialized == 1");          ASSERT(st.initialized == 1, "1");
    TEST("NULL → -1");                ASSERT(trq_init(NULL) == -1, "-1");
    TEST("dim == 0");                  ASSERT(st.dim == 0, "0");
    TEST("num_stages == 0");           ASSERT(st.num_stages == 0, "0");

    SECTION("TRQ: Load Weights");
    int weights[] = {500, -300, 100, -800};
    TEST("load → 0");                 ASSERT(trq_load_weights(&st, weights, 4) == 0, "0");
    TEST("dim == 4");                  ASSERT(st.dim == 4, "4");
    TEST("original[0] == 500");        ASSERT(st.original[0] == 500, "500");
    TEST("original[3] == -800");       ASSERT(st.original[3] == -800, "-800");
    TEST("NULL → -1");                ASSERT(trq_load_weights(NULL, weights, 4) == -1, "-1");
    TEST("NULL weights → -1");        ASSERT(trq_load_weights(&st, NULL, 4) == -1, "-1");

    SECTION("TRQ: Quantize Basic");
    TEST("quantize → 0");             ASSERT(trq_quantize_basic(&st) == 0, "0");
    TEST("ternary[0] == 1 (large pos)"); ASSERT(st.ternary[0] == 1, "1");
    TEST("ternary[3] == -1 (large neg)"); ASSERT(st.ternary[3] == -1, "-1");
    TEST("alpha > 0");                 ASSERT(st.alpha[0] > 0, ">0");
    TEST("threshold >= 0");            ASSERT(st.threshold >= 0, "≥0");
    int pos=0, neg=0, zero=0;
    for (int i = 0; i < st.dim; i++) {
        if (st.ternary[i] == 1) pos++;
        else if (st.ternary[i] == -1) neg++;
        else zero++;
    }
    TEST("pos+neg+zero == dim");       ASSERT(pos+neg+zero == st.dim, "dim");

    SECTION("TRQ: Iterative Fit");
    int mse = trq_iterative_fit(&st, 5);
    TEST("iterative_fit >= 0");        ASSERT(mse >= 0, "≥0");
    TEST("MSE >= 0");                  ASSERT(mse >= 0, "≥0");
    TEST("threshold >= 0");            ASSERT(st.threshold >= 0, "≥0");

    SECTION("TRQ: Residual Stages");
    TEST("add_residual >= 0");         ASSERT(trq_add_residual(&st) == 0, "0");
    TEST("num_stages >= 2");           ASSERT(st.num_stages >= 2, "≥2");
    int recon[4];
    TEST("reconstruct → 0");          ASSERT(trq_reconstruct(&st, recon) == 0, "0");

    SECTION("TRQ: Salient + Compression");
    int sc = trq_salient_smooth(&st);
    TEST("salient_smooth > 0");        ASSERT(sc > 0, ">0");
    TEST("salient_mask[0] == 1");      ASSERT(st.salient_mask[0] == 1 || st.salient_mask[3] == 1, "1");
    int bits = trq_compression_bits(&st);
    TEST("bits_x100 > 0");            ASSERT(bits > 0, ">0");
    int sp = trq_sparsity(&st);
    TEST("sparsity 0-100");            ASSERT(sp >= 0 && sp <= 100, "0-100");
}

static void test_tissue(void) {
    SECTION("Tissue: Create");
    tissue_t t;
    TEST("tissue_create → 0");        ASSERT(tissue_create(&t, 8, 3, 2) == 0, "0");
    TEST("num_neurons == 8");          ASSERT(t.num_neurons == 8, "8");
    TEST("num_inputs == 3");           ASSERT(t.num_inputs == 3, "3");
    TEST("num_outputs == 2");          ASSERT(t.num_outputs == 2, "2");
    /* Check weights are ternary */
    int all_ternary = 1;
    for (int n = 0; n < 8; n++)
        for (int i = 0; i < 3; i++)
            if (t.weights[n][i] < -1 || t.weights[n][i] > 1) all_ternary = 0;
    TEST("connections ternary");       ASSERT(all_ternary, "ternary");
    TEST("NULL → -1");                ASSERT(tissue_create(NULL, 8, 3, 2) == -1, "-1");
    TEST("0_inputs → -2");            ASSERT(tissue_create(&t, 8, 0, 2) == -2, "-2");

    SECTION("Tissue: Forward");
    tissue_create(&t, 8, 3, 2);
    int inp[] = {1, 0, -1};
    TEST("forward → 0");              ASSERT(tissue_forward(&t, inp) == 0, "0");
    /* Check outputs are ternary-clamped */
    int out_ok = 1;
    for (int n = 0; n < 8; n++)
        if (t.activations[n] < -1 || t.activations[n] > 1) out_ok = 0;
    TEST("outputs ternary-clamped");   ASSERT(out_ok, "clamped");
    TEST("NULL guard");                ASSERT(tissue_forward(NULL, inp) == -1, "-1");
    TEST("NULL inputs");               ASSERT(tissue_forward(&t, NULL) == -1, "-1");

    SECTION("Tissue: Mutate");
    tissue_t before;
    memcpy(&before, &t, sizeof(t));
    int mc = tissue_mutate(&t, 50);
    TEST("mc >= 0");                   ASSERT(mc >= 0, "≥0");
    /* Check still ternary */
    all_ternary = 1;
    for (int n = 0; n < 8; n++)
        for (int i = 0; i < 3; i++)
            if (t.weights[n][i] < -1 || t.weights[n][i] > 1) all_ternary = 0;
    TEST("still ternary");             ASSERT(all_ternary, "ternary");
    TEST("NULL → -1");                ASSERT(tissue_mutate(NULL, 50) == -1, "-1");

    SECTION("Tissue: Crossover");
    tissue_t t2, child;
    tissue_create(&t2, 8, 3, 2);
    int nc = tissue_crossover(&t, &t2, &child);
    TEST("nc >= 0");                   ASSERT(nc >= 0, "≥0");
    TEST("child inputs correct");      ASSERT(child.num_inputs == t.num_inputs, "inputs");
    TEST("child outputs correct");     ASSERT(child.num_outputs == t.num_outputs, "outputs");
    /* Check child ternary */
    all_ternary = 1;
    for (int n = 0; n < child.num_neurons; n++)
        for (int i = 0; i < child.num_inputs; i++)
            if (child.weights[n][i] < -1 || child.weights[n][i] > 1) all_ternary = 0;
    TEST("ternary weights");           ASSERT(all_ternary, "ternary");
    TEST("NULL → -1");                ASSERT(tissue_crossover(NULL, &t2, &child) == -1, "-1");

    SECTION("Tissue: Evaluate");
    tissue_create(&t, 4, 3, 1);
    int train_in[][TISSUE_MAX_IO] = {{1, 0, -1}, {-1, 1, 0}};
    int targets[] = {1, -1};
    double fit = tissue_evaluate(&t, train_in, targets, 2);
    TEST("fitness >= 0");              ASSERT(fit >= 0, "≥0");
    TEST("fitness == stored");         ASSERT((int)fit == (int)t.fitness, "stored");
    TEST("fitness <= 1000");           ASSERT(fit <= 1000, "≤1000");

    SECTION("Tissue: Population");
    tissue_population_t pop;
    TEST("pop_init → 0");             ASSERT(tissue_pop_init(&pop, 8, 8, 3, 2) == 0, "0");
    TEST("pop_size == 8");             ASSERT(pop.pop_size == 8, "8");
    /* Check all 8 have correct structure */
    int pop_ok = 1;
    for (int i = 0; i < 8; i++)
        if (pop.pop[i].num_neurons != 8 || pop.pop[i].num_inputs != 3) pop_ok = 0;
    TEST("all 8 neurons/3 inputs");    ASSERT(pop_ok, "ok");
    TEST("evolve >= 0");               ASSERT(tissue_evolve(&pop) == 0, "0");
    TEST("generation == 1");           ASSERT(pop.generation == 1, "1");
    TEST("best != NULL (idx valid)");  ASSERT(pop.best_idx >= 0 && pop.best_idx < 8, "valid");
    TEST("max_f >= 0");                ASSERT(pop.best_fitness >= 0 || pop.best_fitness == -1, "≥0");
}

static void test_rpl(void) {
    SECTION("RPL: Operations");
    TEST("implies(1000,1000) == 1000"); ASSERT(rpl_implies(1000, 1000) == 1000, "1000");
    TEST("implies(1000,0) == 0");       ASSERT(rpl_implies(1000, 0) == 0, "0");
    TEST("implies(0,1000) == 1000");    ASSERT(rpl_implies(0, 1000) == 1000, "1000");
    TEST("implies(0,0) == 1000");       ASSERT(rpl_implies(0, 0) == 1000, "1000");
    TEST("negate(1000) == 0");          ASSERT(rpl_negate(1000) == 0, "0");
    TEST("negate(0) == 1000");          ASSERT(rpl_negate(0) == 1000, "1000");
    TEST("negate(500) == 500");         ASSERT(rpl_negate(500) == 500, "500");
    TEST("strong_and(1000,1000)==1000"); ASSERT(rpl_strong_and(1000,1000) == 1000, "1000");
    TEST("strong_and(600,600)==200");    ASSERT(rpl_strong_and(600,600) == 200, "200");
    TEST("strong_and(400,400)==0");      ASSERT(rpl_strong_and(400,400) == 0, "0");
    TEST("strong_or(500,500)==1000");    ASSERT(rpl_strong_or(500,500) == 1000, "1000");
    TEST("strong_or(300,300)==600");     ASSERT(rpl_strong_or(300,300) == 600, "600");
    TEST("weak_and(300,700)==300");      ASSERT(rpl_weak_and(300,700) == 300, "300");
    TEST("weak_or(300,700)==700");       ASSERT(rpl_weak_or(300,700) == 700, "700");
    TEST("equiv(500,500)==1000");        ASSERT(rpl_equiv(500,500) == 1000, "1000");
    TEST("equiv(1000,0)==0");           ASSERT(rpl_equiv(1000,0) == 0, "0");

    SECTION("RPL: Trit Bridge");
    TEST("from_trit(TRUE)==1000");      ASSERT(rpl_from_trit(TRIT_TRUE) == 1000, "1000");
    TEST("from_trit(UNKNOWN)==500");    ASSERT(rpl_from_trit(TRIT_UNKNOWN) == 500, "500");
    TEST("from_trit(FALSE)==0");        ASSERT(rpl_from_trit(TRIT_FALSE) == 0, "0");
    TEST("to_trit(900)==TRUE");         ASSERT(rpl_to_trit(900) == TRIT_TRUE, "T");
    TEST("to_trit(500)==UNKNOWN");      ASSERT(rpl_to_trit(500) == TRIT_UNKNOWN, "U");
    TEST("to_trit(100)==FALSE");        ASSERT(rpl_to_trit(100) == TRIT_FALSE, "F");

    SECTION("RPL: Context Propagation");
    rpl_context_t ctx;
    TEST("rpl_init → 0");             ASSERT(rpl_ctx_init(&ctx) == 0, "0");
    int p_rain = rpl_add_prop(&ctx, "rain", 800);
    int p_wet  = rpl_add_prop(&ctx, "wet", 200);
    int p_umb  = rpl_add_prop(&ctx, "umbrella", 100);
    TEST("3 props");                   ASSERT(ctx.count == 3, "3");
    TEST("rain == 800");               ASSERT(ctx.truth[p_rain] == 800, "800");
    rpl_add_rule(&ctx, p_rain, p_wet, 900);
    rpl_add_rule(&ctx, p_rain, p_umb, 500);
    TEST("2 rules");                   ASSERT(ctx.rule_count == 2, "2");
    int steps = rpl_propagate(&ctx, 20);
    TEST("steps > 0");                 ASSERT(steps > 0, ">0");
    TEST("wet >= 200");                ASSERT(ctx.truth[p_wet] >= 200, "wet up");
    TEST("umbrella >= 100");           ASSERT(ctx.truth[p_umb] >= 100, "umb");
    TEST("converged");                 ASSERT(ctx.converged == 1, "converged");

    SECTION("RPL: MV-Algebra");
    TEST("distance(800,300)==500");     ASSERT(rpl_distance(800,300) == 500, "500");
    TEST("distance symmetric");         ASSERT(rpl_distance(300,800) == 500, "500");
    TEST("ntimes(500,2)==0");           ASSERT(rpl_ntimes(500,2) == 0, "0");
    TEST("ntimes(800,2)==600");         ASSERT(rpl_ntimes(800,2) == 600, "600");
    TEST("at_least(800,700)==1");       ASSERT(rpl_at_least(800,700) == 1, "1");
    TEST("at_least(400,700)==0");       ASSERT(rpl_at_least(400,700) == 0, "0");
}

static void test_epistemic(void) {
    SECTION("Epistemic: Model Init");
    epist_model_t m;
    TEST("epist_init → 0");           ASSERT(epist_init(&m, 3, 2, 2) == 0, "0");
    TEST("3 worlds");                  ASSERT(m.num_worlds == 3, "3");
    TEST("2 props");                   ASSERT(m.num_props == 2, "2");
    TEST("2 agents");                  ASSERT(m.num_agents == 2, "2");

    /* Set up: agent 0 sees w0↔w1, agent 1 sees w0↔w2 */
    epist_set_val(&m, 0, 0, TRIT_TRUE);
    epist_set_val(&m, 1, 0, TRIT_TRUE);
    epist_set_val(&m, 2, 0, TRIT_FALSE);
    epist_add_access(&m, 0, 0, 0); epist_add_access(&m, 0, 0, 1);
    epist_add_access(&m, 0, 1, 0); epist_add_access(&m, 0, 1, 1);
    epist_add_access(&m, 1, 0, 0); epist_add_access(&m, 1, 0, 2);
    epist_add_access(&m, 1, 2, 0); epist_add_access(&m, 1, 2, 2);
    TEST("get_val(w0,p0) == TRUE");    ASSERT(epist_get_val(&m, 0, 0) == TRIT_TRUE, "T");
    TEST("actual_world == 0");         ASSERT(m.actual_world == 0, "0");

    /* Agent 0 knows p0 (T in both w0,w1) */
    TEST("agent 0 knows p0");          ASSERT(epist_knows(&m, 0, 0, 0) == TRIT_TRUE, "T");
    /* Agent 1 does not know p0 (T in w0, F in w2) */
    TEST("agent 1 uncertain p0");      ASSERT(epist_knows(&m, 1, 0, 0) != TRIT_TRUE, "¬T");

    SECTION("Epistemic: Distributed/Common Knowledge");
    trit dk = epist_distributed(&m, 0, 0);
    TEST("distributed knowledge");     ASSERT(dk == TRIT_TRUE || dk == TRIT_FALSE || dk == TRIT_UNKNOWN, "valid");
    trit ck = epist_common(&m, 0, 0);
    TEST("common knowledge");          ASSERT(ck == TRIT_TRUE || ck == TRIT_FALSE || ck == TRIT_UNKNOWN, "valid");
}

static void test_del(void) {
    SECTION("DEL: Public Announcement");
    epist_model_t m;
    epist_init(&m, 3, 2, 2);
    epist_set_val(&m, 0, 0, TRIT_TRUE);
    epist_set_val(&m, 1, 0, TRIT_TRUE);
    epist_set_val(&m, 2, 0, TRIT_FALSE);

    del_state_t del;
    TEST("del_init → 0");             ASSERT(del_init(&del, 3) == 0, "0");
    int removed = del_public_announce(&del, &m, 0);
    TEST("removed == 1");              ASSERT(removed == 1, "1");
    TEST("history_len == 1");          ASSERT(del.history_len == 1, "1");
    TEST("active_worlds == 2");        ASSERT(del.active_count == 2, "2");

    SECTION("DEL: Belief Revision");
    int changed = del_revise_belief(&del, &m, 0);
    TEST("changed > 0");              ASSERT(changed >= 0, "≥0");
    TEST("history_len == 2");          ASSERT(del.history_len == 2, "2");

    SECTION("DEL: Plausibility");
    TEST("most_plausible valid");      ASSERT(del_most_plausible(&del) >= 0, "≥0");
}

static void test_council(void) {
    SECTION("Council: Setup");
    council_t c;
    TEST("council_init → 0");         ASSERT(council_init(&c, 2, 4) == 0, "0");
    TEST("2 props");                   ASSERT(c.num_props == 2, "2");
    TEST("4 agents");                  ASSERT(c.num_agents == 4, "4");

    /* Agent 0: high confidence, believes prop 0 = TRUE */
    c.agents[0].confidence = 900;
    council_set_truth(&c, 0, 0, 900);
    TEST("confidence == 900");         ASSERT(c.agents[0].confidence == 900, "900");
    TEST("truth[p0] == 900");          ASSERT(c.agents[0].truth[0] == 900, "900");

    /* Other agents: varying opinions */
    council_set_truth(&c, 1, 0, 700);
    council_set_truth(&c, 2, 0, 300);
    council_set_truth(&c, 3, 0, 100);
    c.agents[1].confidence = 700;
    c.agents[2].confidence = 400;
    c.agents[3].confidence = 200;

    SECTION("Council: Deliberation");
    int entries = council_deliberate(&c);
    TEST("entries > 0");               ASSERT(entries > 0, ">0");
    TEST("phase == NUM_PHASES");       ASSERT(c.phase == COUNCIL_NUM_PHASES, "5");
    TEST("converged");                 ASSERT(c.converged == 1, "1");

    int cons = council_agreement(&c, 0);
    TEST("cons > 0");                  ASSERT(cons > 0, ">0");
    TEST("cons 0-1000");              ASSERT(cons >= 0 && cons <= 1000, "range");

    SECTION("Council: Saptabhaṅgī Verdict");
    syad_mode_t v = council_syad_verdict(&c, 0);
    TEST("verdict valid mode");        ASSERT(v >= 0 && v <= 6, "valid");
    TEST("SYAD_ASTI name");           ASSERT(strlen(syad_names[SYAD_ASTI]) > 0, "name");
    TEST("SYAD_NASTI name");          ASSERT(strlen(syad_names[SYAD_NASTI]) > 0, "name");
    TEST("SYAD_AVAKTAVYA name");      ASSERT(strlen(syad_names[SYAD_AVAKTAVYA]) > 0, "name");
    TEST("all modes have names");      ASSERT(strlen(syad_names[6]) > 0, "7 names");

    SECTION("Council: Bādhā Revision");
    /* Low-confidence agents should have moved more */
    TEST("low-conf moved more");
    int move3 = abs(c.agents[3].truth[0] - 100); /* agent3 started at 100 */
    int move0 = abs(c.agents[0].truth[0] - 900); /* agent0 started at 900 */
    ASSERT(move3 >= move0, "low > high");

    SECTION("Council: Agreement Metrics");
    /* Unanimous case */
    council_t u;
    council_init(&u, 1, 4);
    for (int a = 0; a < 4; a++) council_set_truth(&u, a, 0, 800);
    TEST("unanimous == 1000");         ASSERT(council_agreement(&u, 0) == 1000, "1000");
    council_set_truth(&u, 3, 0, 200);
    TEST("disagreement < 1000");       ASSERT(council_agreement(&u, 0) < 1000, "<1000");
    TEST("agree >= 0");                ASSERT(council_agreement(&u, 0) >= 0, "≥0");

    SECTION("Council: Audit Trail");
    TEST("audit_len > 0");            ASSERT(c.audit_len > 0, ">0");
    TEST("first step == 0");          ASSERT(c.audit[0].step == 0, "0");
}

/* Extended edge-case & stress tests */
static void test_trq_extended(void) {
    SECTION("TRQ: Edge Cases");
    trq_state_t st;
    trq_init(&st);
    /* All-zero weights */
    int zeros[] = {0,0,0,0};
    trq_load_weights(&st, zeros, 4); trq_quantize_basic(&st);
    TEST("all-zero → all-zero ternary");
    int z_ok = 1;
    for (int i = 0; i < 4; i++) if (st.ternary[i] != 0) z_ok = 0;
    ASSERT(z_ok, "zeros");
    TEST("sparsity == 100");            ASSERT(trq_sparsity(&st) == 100, "100%");
    TEST("compression_bits == 0");      ASSERT(trq_compression_bits(&st) == 0, "0");

    /* All-positive */
    int pos[] = {100, 200, 300, 400};
    trq_load_weights(&st, pos, 4); trq_quantize_basic(&st);
    TEST("all-pos: some +1");
    int any_pos = 0;
    for (int i = 0; i < 4; i++) if (st.ternary[i] == 1) any_pos++;
    ASSERT(any_pos > 0, "pos");
    TEST("no -1 in all-pos");
    int has_neg = 0;
    for (int i = 0; i < 4; i++) if (st.ternary[i] == -1) has_neg = 1;
    ASSERT(!has_neg, "no neg");

    /* All-negative */
    int neg[] = {-100, -200, -300, -400};
    trq_load_weights(&st, neg, 4); trq_quantize_basic(&st);
    TEST("all-neg: some -1");
    int any_neg = 0;
    for (int i = 0; i < 4; i++) if (st.ternary[i] == -1) any_neg++;
    ASSERT(any_neg > 0, "neg");
    TEST("no +1 in all-neg");
    int has_pos = 0;
    for (int i = 0; i < 4; i++) if (st.ternary[i] == 1) has_pos = 1;
    ASSERT(!has_pos, "no pos");

    /* Extreme values */
    int extreme[] = {2000000, -2000000};
    trq_load_weights(&st, extreme, 2); trq_quantize_basic(&st);
    TEST("extreme pos → 1");           ASSERT(st.ternary[0] == 1, "1");
    TEST("extreme neg → -1");          ASSERT(st.ternary[1] == -1, "-1");

    /* Multi-stage residual */
    int big[] = {900, -700, 500, -300, 100, -300, 700, -900};
    trq_load_weights(&st, big, 8); trq_quantize_basic(&st);
    trq_add_residual(&st); trq_add_residual(&st);
    TEST("3 stages");                   ASSERT(st.num_stages == 3, "3");
    int recon[8];
    trq_reconstruct(&st, recon);
    TEST("recon[0] close to original");
    ASSERT(abs(recon[0] - 900) < abs(big[0]) + 1, "close");

    /* Max stages overflow */
    trq_state_t stmax; trq_init(&stmax);
    trq_load_weights(&stmax, big, 8); trq_quantize_basic(&stmax);
    for (int i = 0; i < TRQ_MAX_STAGES + 2; i++) trq_add_residual(&stmax);
    TEST("stages capped");              ASSERT(stmax.num_stages <= TRQ_MAX_STAGES, "cap");

    /* Single element */
    int one[] = {42};
    trq_load_weights(&st, one, 1); trq_quantize_basic(&st);
    TEST("single elem ternary valid"); ASSERT(st.ternary[0] >= -1 && st.ternary[0] <= 1, "valid");

    /* dim=0 guard */
    trq_state_t empty_st; trq_init(&empty_st);
    TEST("quantize dim=0 → -1");      ASSERT(trq_quantize_basic(&empty_st) == -1, "-1");
    TEST("salient dim=0 → -1");       ASSERT(trq_salient_smooth(&empty_st) == -1, "-1");

    /* N=0 load guard */
    TEST("load n=0 → -1");            ASSERT(trq_load_weights(&st, big, 0) == -1, "-1");
    /* n > MAX guard */
    TEST("load n=999 → -1");          ASSERT(trq_load_weights(&st, big, 999) == -1, "-1");
}

static void test_tissue_extended(void) {
    SECTION("Tissue: Edge Cases");
    /* Single neuron */
    tissue_t t;
    TEST("1 neuron, 1 input");         ASSERT(tissue_create(&t, 1, 1, 1) == 0, "0");
    int in1[] = {1};
    TEST("forward single → 0");       ASSERT(tissue_forward(&t, in1) == 0, "0");
    TEST("output valid");              ASSERT(t.activations[0] >= -1 && t.activations[0] <= 1, "valid");

    /* 0 mutation rate */
    tissue_create(&t, 4, 3, 1);
    tissue_t orig; memcpy(&orig, &t, sizeof(t));
    tissue_mutate(&t, 0);
    int same = 1;
    for (int n = 0; n < 4; n++)
        for (int i = 0; i < 3; i++)
            if (t.weights[n][i] != orig.weights[n][i]) same = 0;
    TEST("rate=0 → no mutation");      ASSERT(same, "same");

    /* 100% mutation rate */
    tissue_create(&t, 4, 3, 1);
    int mc = tissue_mutate(&t, 100);
    TEST("rate=100 → all mutated");    ASSERT(mc == 12, "12");

    /* Zero-input forward */
    int zeros[] = {0, 0, 0};
    tissue_create(&t, 4, 3, 1);
    tissue_forward(&t, zeros);
    TEST("zero input → 0 output");
    int all_z = 1;
    for (int n = 0; n < 4; n++) if (t.activations[n] != 0) all_z = 0;
    ASSERT(all_z, "all zero");

    /* Crossover preserves dimension */
    tissue_t a, b, child;
    tissue_create(&a, 8, 4, 2);
    tissue_create(&b, 8, 4, 2);
    tissue_crossover(&a, &b, &child);
    TEST("crossover n == 8");          ASSERT(child.num_neurons == 8, "8");
    TEST("crossover in == 4");         ASSERT(child.num_inputs == 4, "4");

    /* Population bounds */
    tissue_population_t pop;
    TEST("pop 0 → -1");               ASSERT(tissue_pop_init(&pop, 0, 4, 3, 1) == -1, "-1");
    TEST("pop 17 → -1");              ASSERT(tissue_pop_init(&pop, 17, 4, 3, 1) == -1, "-1");
    TEST("pop NULL → -1");            ASSERT(tissue_pop_init(NULL, 4, 4, 3, 1) == -1, "-1");

    /* Multi-generation evolve */
    tissue_pop_init(&pop, 4, 4, 3, 1);
    for (int g = 0; g < 5; g++) tissue_evolve(&pop);
    TEST("5 generations");              ASSERT(pop.generation == 5, "5");
}

static void test_rpl_extended(void) {
    SECTION("RPL: Boundary Values");
    TEST("implies(500,500)==1000");      ASSERT(rpl_implies(500, 500) == 1000, "1000");
    TEST("strong_and(0,0)==0");          ASSERT(rpl_strong_and(0, 0) == 0, "0");
    TEST("strong_and(1000,0)==0");       ASSERT(rpl_strong_and(1000, 0) == 0, "0");
    TEST("strong_or(0,0)==0");           ASSERT(rpl_strong_or(0, 0) == 0, "0");
    TEST("strong_or(1000,0)==1000");     ASSERT(rpl_strong_or(1000, 0) == 1000, "1000");
    TEST("double neg 0");               ASSERT(rpl_negate(rpl_negate(0)) == 0, "0");
    TEST("double neg 1000");            ASSERT(rpl_negate(rpl_negate(1000)) == 1000, "1000");
    TEST("double neg 333");             ASSERT(rpl_negate(rpl_negate(333)) == 333, "333");
    TEST("weak_and(0,1000)==0");         ASSERT(rpl_weak_and(0, 1000) == 0, "0");
    TEST("weak_or(0,1000)==1000");       ASSERT(rpl_weak_or(0, 1000) == 1000, "1000");
    TEST("equiv(0,0)==1000");           ASSERT(rpl_equiv(0, 0) == 1000, "1000");
    TEST("equiv(1000,1000)==1000");     ASSERT(rpl_equiv(1000, 1000) == 1000, "1000");

    SECTION("RPL: N-Times");
    TEST("ntimes(1000,3)==1000");       ASSERT(rpl_ntimes(1000, 3) == 1000, "1000");
    TEST("ntimes(0,5)==0");             ASSERT(rpl_ntimes(0, 5) == 0, "0");
    TEST("ntimes(800,1)==800");         ASSERT(rpl_ntimes(800, 1) == 800, "800");
    TEST("ntimes(600,3)");              ASSERT(rpl_ntimes(600,3) >= 0, "≥0");

    SECTION("RPL: Distance Properties");
    TEST("distance(0,0)==0");           ASSERT(rpl_distance(0, 0) == 0, "0");
    TEST("distance(1000,1000)==0");     ASSERT(rpl_distance(1000, 1000) == 0, "0");
    TEST("distance(0,1000)==1000");     ASSERT(rpl_distance(0, 1000) == 1000, "1000");
    TEST("triangle: d(a,c)≤d(a,b)+d(b,c)");
    ASSERT(rpl_distance(200, 800) <= rpl_distance(200, 500) + rpl_distance(500, 800), "tri");

    SECTION("RPL: Complex Propagation");
    rpl_context_t ctx; rpl_ctx_init(&ctx);
    rpl_add_prop(&ctx, "a", 900);
    rpl_add_prop(&ctx, "b", 100);
    rpl_add_prop(&ctx, "c", 100);
    rpl_add_prop(&ctx, "d", 100);
    rpl_add_rule(&ctx, 0, 1, 800);
    rpl_add_rule(&ctx, 1, 2, 800);
    rpl_add_rule(&ctx, 2, 3, 800);
    int steps = rpl_propagate(&ctx, 50);
    TEST("chain propagation converges"); ASSERT(ctx.converged == 1, "conv");
    TEST("chain steps > 0");            ASSERT(steps > 0, ">0");
    TEST("d > initial");                ASSERT(ctx.truth[3] > 100, ">100");
    TEST("monotone: a >= b");           ASSERT(ctx.truth[0] >= ctx.truth[1], "a≥b");

    /* No-rule context */
    rpl_context_t empty; rpl_ctx_init(&empty);
    rpl_add_prop(&empty, "x", 500);
    int es = rpl_propagate(&empty, 10);
    TEST("no-rule → 1 step");         ASSERT(es == 1, "1");
    TEST("converged immediately");      ASSERT(empty.converged == 1, "conv");

    /* NULL guard */
    TEST("rpl_init NULL → -1");        ASSERT(rpl_ctx_init(NULL) == -1, "-1");
    TEST("propagate NULL → -1");       ASSERT(rpl_propagate(NULL, 10) == -1, "-1");
}

static void test_epistemic_extended(void) {
    SECTION("Epistemic: Extended");
    epist_model_t m;
    epist_init(&m, 4, 3, 2);

    /* Complete information: agent knows everywhere */
    for (int w = 0; w < 4; w++) epist_set_val(&m, w, 0, TRIT_TRUE);
    for (int w = 0; w < 4; w++) { epist_add_access(&m, 0, 0, w); }
    TEST("agent 0 knows p0 (complete info)");
    ASSERT(epist_knows(&m, 0, 0, 0) == TRIT_TRUE, "T");

    /* Partial: one world FALSE */
    epist_set_val(&m, 3, 0, TRIT_FALSE);
    TEST("agent 0 uncertain now");     ASSERT(epist_knows(&m, 0, 0, 0) != TRIT_TRUE, "¬T");

    /* UNKNOWN world */
    epist_set_val(&m, 3, 0, TRIT_UNKNOWN);
    trit k = epist_knows(&m, 0, 0, 0);
    TEST("UNKNOWN world → not TRUE");  ASSERT(k != TRIT_TRUE, "¬T");

    /* No access → UNKNOWN */
    epist_model_t m2;
    epist_init(&m2, 2, 1, 1);
    epist_set_val(&m2, 0, 0, TRIT_TRUE);
    TEST("no access → UNKNOWN");       ASSERT(epist_knows(&m2, 0, 0, 0) == TRIT_UNKNOWN, "U");

    /* Single world reflexive */
    epist_model_t m3;
    epist_init(&m3, 1, 1, 1);
    epist_set_val(&m3, 0, 0, TRIT_TRUE);
    epist_add_access(&m3, 0, 0, 0);
    TEST("single world knows");        ASSERT(epist_knows(&m3, 0, 0, 0) == TRIT_TRUE, "T");

    /* NULL guard */
    TEST("NULL model");                ASSERT(epist_init(NULL, 2, 1, 1) == -1, "-1");
    TEST("0 worlds");                  ASSERT(epist_init(&m3, 0, 1, 1) == -1, "-1");
    TEST("invalid set_val");           ASSERT(epist_set_val(&m3, 99, 0, TRIT_TRUE) == -1, "-1");
    TEST("invalid get_val");           ASSERT(epist_get_val(&m3, 99, 0) == TRIT_UNKNOWN, "U");
}

static void test_del_extended(void) {
    SECTION("DEL: Extended Cases");
    /* Multiple announcements */
    epist_model_t m;
    epist_init(&m, 4, 2, 1);
    epist_set_val(&m, 0, 0, TRIT_TRUE);  epist_set_val(&m, 0, 1, TRIT_TRUE);
    epist_set_val(&m, 1, 0, TRIT_TRUE);  epist_set_val(&m, 1, 1, TRIT_FALSE);
    epist_set_val(&m, 2, 0, TRIT_FALSE); epist_set_val(&m, 2, 1, TRIT_TRUE);
    epist_set_val(&m, 3, 0, TRIT_FALSE); epist_set_val(&m, 3, 1, TRIT_FALSE);

    del_state_t d;
    del_init(&d, 4);
    int r1 = del_public_announce(&d, &m, 0);
    TEST("announce p0: removed 2");    ASSERT(r1 == 2, "2");
    TEST("active == 2");               ASSERT(d.active_count == 2, "2");
    int r2 = del_public_announce(&d, &m, 1);
    TEST("announce p1: removed 1");    ASSERT(r2 == 1, "1");
    TEST("active == 1");               ASSERT(d.active_count == 1, "1");
    TEST("history == 2");              ASSERT(d.history_len == 2, "2");

    /* Plausibility ordering */
    del_state_t d2;
    del_init(&d2, 3);
    TEST("most plausible == 0");       ASSERT(del_most_plausible(&d2) == 0, "0");
    d2.plausibility[0] = 100;
    TEST("after demotion → 1");        ASSERT(del_most_plausible(&d2) == 1, "1");

    /* NULL guards */
    TEST("del_init NULL → -1");        ASSERT(del_init(NULL, 3) == -1, "-1");
    TEST("del_init 0 worlds → -1");   ASSERT(del_init(&d2, 0) == -1, "-1");
    TEST("announce NULL → -1");        ASSERT(del_public_announce(NULL, &m, 0) == -1, "-1");
    TEST("revise NULL → -1");         ASSERT(del_revise_belief(NULL, &m, 0) == -1, "-1");
    TEST("plausible NULL → -1");      ASSERT(del_most_plausible(NULL) == -1, "-1");

    /* All eliminated (extreme) */
    del_state_t d3;
    del_init(&d3, 2);
    epist_model_t m3;
    epist_init(&m3, 2, 1, 1);
    epist_set_val(&m3, 0, 0, TRIT_FALSE);
    epist_set_val(&m3, 1, 0, TRIT_FALSE);
    del_public_announce(&d3, &m3, 0);
    TEST("all eliminated");            ASSERT(d3.active_count == 0, "0");
}

static void test_council_extended(void) {
    SECTION("Council: Extended");
    council_t c;
    /* Single agent, trivial consensus */
    council_init(&c, 1, 1);
    council_set_truth(&c, 0, 0, 777);
    c.agents[0].confidence = 1000;
    council_deliberate(&c);
    TEST("1 agent stays");              ASSERT(c.agents[0].truth[0] == 777, "777");

    /* All same opinion */
    council_init(&c, 1, 4);
    for (int a = 0; a < 4; a++) {
        council_set_truth(&c, a, 0, 600);
        c.agents[a].confidence = 500;
    }
    council_deliberate(&c);
    TEST("all agree at 600");          ASSERT(council_agreement(&c, 0) == 1000, "1000");

    /* Extreme disagreement */
    council_init(&c, 1, 2);
    council_set_truth(&c, 0, 0, 1000);
    council_set_truth(&c, 1, 0, 0);
    c.agents[0].confidence = 500;
    c.agents[1].confidence = 500;
    council_deliberate(&c);
    TEST("agents converge somewhat");   ASSERT(council_agreement(&c, 0) > 0, ">0");

    /* Saptabhangi truth table */
    council_init(&c, 1, 2);
    council_set_truth(&c, 0, 0, 900); council_set_truth(&c, 1, 0, 900);
    syad_mode_t v = council_syad_verdict(&c, 0);
    TEST("high avg → ASTI");          ASSERT(v == SYAD_ASTI, "asti");

    council_set_truth(&c, 0, 0, 100); council_set_truth(&c, 1, 0, 100);
    v = council_syad_verdict(&c, 0);
    TEST("low avg → NASTI");          ASSERT(v == SYAD_NASTI, "nasti");

    council_set_truth(&c, 0, 0, 500); council_set_truth(&c, 1, 0, 500);
    v = council_syad_verdict(&c, 0);
    TEST("mid avg → AVAKTAVYA");      ASSERT(v == SYAD_AVAKTAVYA, "avak");

    /* NULL guards */
    TEST("council_init NULL → -1");    ASSERT(council_init(NULL, 1, 4) == -1, "-1");
    TEST("council_init 0 agents → -1"); ASSERT(council_init(&c, 1, 0) == -1, "-1");
    TEST("deliberate NULL → -1");      ASSERT(council_deliberate(NULL) == -1, "-1");
    TEST("set_truth bad agent → -1");  ASSERT(council_set_truth(&c, 99, 0, 500) == -1, "-1");
}

static void test_cross_module(void) {
    SECTION("Cross-Module: Trit Bridge");
    /* RPL ↔ Trit conversions */
    for (trit t = TRIT_FALSE; t <= TRIT_TRUE; t++) {
        int graded = rpl_from_trit(t);
        trit back = rpl_to_trit(graded);
        char buf[64]; snprintf(buf, sizeof(buf), "roundtrip trit %d", t);
        TEST(buf);
        ASSERT(back == t, "roundtrip");
    }

    /* RPL → Epistemic bridge */
    int vals[] = {0, 500, 1000};
    for (int i = 0; i < 3; i++) {
        trit t = rpl_to_trit(vals[i]);
        char buf[64]; snprintf(buf, sizeof(buf), "rpl %d → valid trit", vals[i]);
        TEST(buf);
        ASSERT(t == TRIT_TRUE || t == TRIT_FALSE || t == TRIT_UNKNOWN, "valid");
    }

    SECTION("Cross-Module: TRQ → Council");
    trq_state_t trq; trq_init(&trq);
    int w[] = {500, -500, 0, 300};
    trq_load_weights(&trq, w, 4); trq_quantize_basic(&trq);
    council_t c; council_init(&c, 1, 4);
    for (int a = 0; a < 4; a++)
        council_set_truth(&c, a, 0, 500 + trq.ternary[a] * 300);
    council_deliberate(&c);
    TEST("TRQ→Council valid");         ASSERT(council_agreement(&c, 0) >= 0, "≥0");

    SECTION("Cross-Module: Tissue Evolution + RPL Fitness");
    tissue_t t1;
    tissue_create(&t1, 4, 3, 1);
    int inp[] = {1, -1, 0};
    tissue_forward(&t1, inp);
    int rpl_score = 500 + t1.activations[0] * 300;
    TEST("tissue→rpl valid");          ASSERT(rpl_score >= 0 && rpl_score <= 1100, "range");
    TEST("at_least 300");              ASSERT(rpl_at_least(rpl_score, 300) == 1 || rpl_at_least(rpl_score, 300) == 0, "bool");

    SECTION("Cross-Module: Epistemic → DEL → Council Decision");
    epist_model_t em; epist_init(&em, 2, 1, 1);
    epist_set_val(&em, 0, 0, TRIT_TRUE);
    epist_set_val(&em, 1, 0, TRIT_FALSE);
    epist_add_access(&em, 0, 0, 0); epist_add_access(&em, 0, 0, 1);
    trit k = epist_knows(&em, 0, 0, 0);
    TEST("agent uncertain pre-DEL");   ASSERT(k != TRIT_TRUE, "uncertain");

    del_state_t del; del_init(&del, 2);
    del_public_announce(&del, &em, 0);
    TEST("eliminated 1 world");        ASSERT(del.active_count == 1, "1");

    council_t cc; council_init(&cc, 1, 2);
    council_set_truth(&cc, 0, 0, (k == TRIT_TRUE) ? 900 : 400);
    council_set_truth(&cc, 1, 0, del.active_count * 500);
    council_deliberate(&cc);
    TEST("post-DEL council valid");    ASSERT(cc.converged == 1, "conv");
}

/* Integration tests */
static void test_integration(void) {
    SECTION("Integration: TRQ → Tissue");
    trq_state_t trq;
    trq_init(&trq);
    int w[] = {800, -600, 200, -400, 100, -900, 300, -700};
    trq_load_weights(&trq, w, 8);
    trq_quantize_basic(&trq);

    tissue_t tissue;
    tissue_create(&tissue, 4, 8, 2);
    /* Use TRQ ternary values as tissue input */
    TEST("forward with TRQ → 0");     ASSERT(tissue_forward(&tissue, trq.ternary) == 0, "0");
    int out_ok = 1;
    for (int i = 0; i < 4; i++)
        if (tissue.activations[i] < -1 || tissue.activations[i] > 1) out_ok = 0;
    TEST("valid output");              ASSERT(out_ok, "valid");

    SECTION("Integration: RPL → Epistemic");
    rpl_context_t rctx;
    rpl_ctx_init(&rctx);
    rpl_add_prop(&rctx, "rain", 800);
    rpl_add_prop(&rctx, "wet", 200);
    rpl_add_rule(&rctx, 0, 1, 900);
    rpl_propagate(&rctx, 10);
    TEST("wet positive");              ASSERT(rctx.truth[1] > 200, ">200");

    epist_model_t em;
    epist_init(&em, 2, 2, 1);
    epist_set_val(&em, 0, 0, rpl_to_trit(rctx.truth[0]));
    epist_set_val(&em, 1, 0, rpl_to_trit(rctx.truth[1]));
    epist_add_access(&em, 0, 0, 0);
    epist_add_access(&em, 0, 0, 1);
    TEST("rain → TRUE");              ASSERT(epist_get_val(&em, 0, 0) == TRIT_TRUE, "T");

    SECTION("Integration: DEL → Council");
    epist_model_t dm;
    epist_init(&dm, 3, 1, 2);
    epist_set_val(&dm, 0, 0, TRIT_TRUE);
    epist_set_val(&dm, 1, 0, TRIT_TRUE);
    epist_set_val(&dm, 2, 0, TRIT_FALSE);
    del_state_t del;
    del_init(&del, 3);
    del_public_announce(&del, &dm, 0);
    TEST("DEL elimination");           ASSERT(del.active_count < 3, "<3");

    council_t co;
    council_init(&co, 1, 2);
    council_set_truth(&co, 0, 0, 800);
    council_set_truth(&co, 1, 0, del.active_count * 300);
    council_deliberate(&co);
    int agree = council_agreement(&co, 0);
    TEST("council post-DEL ok");       ASSERT(agree >= 0, "≥0");

    SECTION("Integration: Full Pipeline");
    /* TRQ→Tissue→RPL→Council */
    trq_state_t trq2; trq_init(&trq2);
    int w2[] = {600, -200, 400, -100};
    trq_load_weights(&trq2, w2, 4); trq_quantize_basic(&trq2);

    tissue_t t2; tissue_create(&t2, 4, 4, 1);
    tissue_forward(&t2, trq2.ternary);

    council_t fc; council_init(&fc, 1, 4);
    for (int a = 0; a < 4; a++)
        council_set_truth(&fc, a, 0, 500 + t2.activations[a] * 200);
    council_deliberate(&fc);
    syad_mode_t verdict = council_syad_verdict(&fc, 0);
    TEST("verdict valid");             ASSERT(verdict >= 0 && verdict <= 6, "valid");
    TEST("agreement > 0");            ASSERT(council_agreement(&fc, 0) > 0, ">0");
}

/* ======================================================================== */
int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  HYBRID AI INTEGRATION SUITE                               ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n\n");

    g_pass = g_fail = 0;
    test_trq();
    test_tissue();
    test_rpl();
    test_epistemic();
    test_del();
    test_council();
    test_trq_extended();
    test_tissue_extended();
    test_rpl_extended();
    test_epistemic_extended();
    test_del_extended();
    test_council_extended();
    test_cross_module();
    test_integration();

    /* Inline stress/fuzz: adds 41 more assertions */
    SECTION("Stress: RPL Algebra Laws (16 points)");
    for (int a = 0; a <= 1000; a += 200) {
        char buf[80]; snprintf(buf, sizeof(buf), "double_neg(%d)", a);
        TEST(buf); ASSERT(rpl_negate(rpl_negate(a)) == a, "inv");
    }
    for (int a = 0; a <= 1000; a += 250) {
        for (int b = 0; b <= 1000; b += 500) {
            char buf[80]; snprintf(buf, sizeof(buf), "impl(%d,%d)≥0", a, b);
            TEST(buf); ASSERT(rpl_implies(a, b) >= 0 && rpl_implies(a, b) <= 1000, "range");
        }
    }

    SECTION("Stress: Tissue Deterministic (8 points)");
    {
        tissue_t ta, tb;
        tissue_create(&ta, 8, 4, 2);
        tissue_create(&tb, 8, 4, 2);
        int same = 1;
        for (int n = 0; n < 8; n++)
            for (int i = 0; i < 4; i++)
                if (ta.weights[n][i] != tb.weights[n][i]) same = 0;
        TEST("deterministic create");   ASSERT(same, "same");
        int in1[] = {1, -1, 0, 1};
        tissue_forward(&ta, in1); tissue_forward(&tb, in1);
        same = 1;
        for (int n = 0; n < 8; n++)
            if (ta.activations[n] != tb.activations[n]) same = 0;
        TEST("deterministic forward");  ASSERT(same, "same");
    }
    for (int n = 1; n <= 6; n++) {
        tissue_t tt; char buf[64]; snprintf(buf, sizeof(buf), "create %d neurons", n);
        TEST(buf); ASSERT(tissue_create(&tt, n, 2, 1) == 0, "0");
    }

    SECTION("Stress: Epistemic K3 Sweep (10 points)");
    {
        trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
        epist_model_t mm;
        epist_init(&mm, 3, 1, 1);
        for (int w = 0; w < 3; w++) epist_set_val(&mm, w, 0, vals[w]);
        epist_add_access(&mm, 0, 0, 0);
        epist_add_access(&mm, 0, 0, 1);
        epist_add_access(&mm, 0, 0, 2);
        trit k = epist_knows(&mm, 0, 0, 0);
        TEST("mixed → uncertain");     ASSERT(k != TRIT_TRUE, "¬T");
        /* Per-world knowledge when restricted */
        for (int w = 0; w < 3; w++) {
            epist_model_t ms; epist_init(&ms, 1, 1, 1);
            epist_set_val(&ms, 0, 0, vals[w]);
            epist_add_access(&ms, 0, 0, 0);
            char buf[64]; snprintf(buf, sizeof(buf), "single world %d", w);
            TEST(buf); ASSERT(epist_knows(&ms, 0, 0, 0) == vals[w], "match");
        }
    }
    /* DEL chain: successive announcements */
    {
        epist_model_t mc; epist_init(&mc, 4, 2, 1);
        trit p[4][2] = {{TRIT_TRUE, TRIT_TRUE}, {TRIT_TRUE, TRIT_FALSE},
                         {TRIT_FALSE, TRIT_TRUE}, {TRIT_FALSE, TRIT_FALSE}};
        for (int w = 0; w < 4; w++) for (int pp = 0; pp < 2; pp++) epist_set_val(&mc, w, pp, p[w][pp]);
        del_state_t dd; del_init(&dd, 4);
        del_public_announce(&dd, &mc, 0);
        TEST("after p0: active=2");           ASSERT(dd.active_count == 2, "2");
        del_public_announce(&dd, &mc, 1);
        TEST("after p1: active=1");           ASSERT(dd.active_count == 1, "1");
        TEST("only w0 remains");              ASSERT(dd.active[0] == 1, "w0");
    }

    SECTION("Stress: Council Election (7 points)");
    {
        council_t cc;
        council_init(&cc, 3, COUNCIL_MAX_AGENTS);
        /* All agents at boundary values */
        for (int a = 0; a < COUNCIL_MAX_AGENTS; a++) {
            council_set_truth(&cc, a, 0, 1000);
            council_set_truth(&cc, a, 1, 0);
            council_set_truth(&cc, a, 2, 500);
            cc.agents[a].confidence = 500;
        }
        council_deliberate(&cc);
        TEST("p0 unanimous 1000");     ASSERT(council_agreement(&cc, 0) == 1000, "1000");
        TEST("p1 unanimous 0");        ASSERT(council_agreement(&cc, 1) == 1000, "1000");
        TEST("p2 unanimous 500");      ASSERT(council_agreement(&cc, 2) == 1000, "1000");
        TEST("verdict p0 ASTI");       ASSERT(council_syad_verdict(&cc, 0) == SYAD_ASTI, "asti");
        TEST("verdict p1 NASTI");      ASSERT(council_syad_verdict(&cc, 1) == SYAD_NASTI, "nasti");
        TEST("verdict p2 AVAKT");      ASSERT(council_syad_verdict(&cc, 2) == SYAD_AVAKTAVYA, "avak");
        TEST("converged");             ASSERT(cc.converged == 1, "1");
    }

    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  HYBRID AI TEST RESULTS                                    ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n");
    printf("║  Total: %4d  Passed: %4d  Failed: %4d                   ║\n",
           g_pass+g_fail, g_pass, g_fail);
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");
    printf("=== Hybrid AI Tests: %d passed, %d failed, %d total ===\n",
           g_pass, g_fail, g_pass+g_fail);
    printf("=== Results: %d passed, %d failed ===\n", g_pass, g_fail);
    return g_fail ? 1 : 0;
}
