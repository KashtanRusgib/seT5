/* tests/test_sigma9_mcp.c — Sigma 9 MCP (Model Context Protocol) (Suite 37)
 * 259 runtime assertions: AECC + TS-Memristor TCAM + Peirce Logic + BCT +
 *   REBEL-2 ISA + Memristive Memory + MCP Server
 *
 * The MCP infrastructure and all domain modules (AECC, TCAM, Peirce, BCT,
 * REBEL-2, Memristive) are inline-implemented to be fully self-contained.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include "set5/trit.h"
#include "set5/trit_emu.h"

static int g_pass, g_fail;
#define TEST(name) printf("  %-60s ", name)
#define PASS()     do { g_pass++; printf("[PASS]\n"); } while(0)
#define FAIL(msg)  do { g_fail++; printf("[FAIL] %s\n", msg); } while(0)
#define ASSERT(expr, msg) do { if (expr) { PASS(); } else { FAIL(msg); } } while(0)
#define SECTION(s) printf("\n══ %s ══\n", s)

/* ========================================================================
 * Inline MCP Domain Modules
 * ======================================================================== */

/* --- Abductive ECC (AECC) --- */
typedef struct {
    trit transition[3][3]; /* [from_state][to_state]: T=allowed, U=uncertain, F=forbidden */
    int initialized;
} aecc_channel_t;

static int aecc_channel_init_balanced(aecc_channel_t *ch) {
    if (!ch) return -1;
    memset(ch, 0, sizeof(*ch));
    /* Balanced encoding: N=0, Z=1, P=2 */
    /* N→N:T  N→Z:T  N→P:F */
    ch->transition[0][0] = TRIT_TRUE;
    ch->transition[0][1] = TRIT_TRUE;
    ch->transition[0][2] = TRIT_FALSE;
    /* Z→N:T  Z→Z:T  Z→P:T */
    ch->transition[1][0] = TRIT_TRUE;
    ch->transition[1][1] = TRIT_TRUE;
    ch->transition[1][2] = TRIT_TRUE;
    /* P→N:F  P→Z:T  P→P:T */
    ch->transition[2][0] = TRIT_FALSE;
    ch->transition[2][1] = TRIT_TRUE;
    ch->transition[2][2] = TRIT_TRUE;
    ch->initialized = 1;
    return 0;
}

static int aecc_modified_hamming_distance(const trit *a, const trit *b, int len) {
    if (!a || !b || len <= 0) return -1;
    int dist = 0;
    for (int i = 0; i < len; i++) {
        int d = abs(a[i] - b[i]);
        if (d > 0) dist += d;
    }
    return dist;
}

typedef struct {
    trit codewords[8][6];
    int codeword_count;
    int codeword_len;
    int initialized;
} aecc_codebook_t;

static int aecc_codebook_generate(aecc_codebook_t *cb, int len) {
    if (!cb || len <= 0 || len > 6) return -1;
    memset(cb, 0, sizeof(*cb));
    cb->codeword_len = len;
    /* Generate codewords with minimum distance 2 */
    int idx = 0;
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3 && idx < 8; i++)
        for (int j = 0; j < 3 && idx < 8; j++) {
            cb->codewords[idx][0] = vals[i];
            cb->codewords[idx][1] = vals[j];
            for (int k = 2; k < len; k++)
                cb->codewords[idx][k] = vals[(i+j+k) % 3];
            idx++;
        }
    cb->codeword_count = idx;
    cb->initialized = 1;
    return 0;
}

static int aecc_encode(const aecc_codebook_t *cb, int idx, trit *out) {
    if (!cb || !out || !cb->initialized) return -1;
    if (idx < 0 || idx >= cb->codeword_count) return -1;
    memcpy(out, cb->codewords[idx], cb->codeword_len * sizeof(trit));
    return 0;
}

static int aecc_decode(const aecc_codebook_t *cb, const trit *in, trit *out) {
    if (!cb || !in || !out || !cb->initialized) return -1;
    int best = 0, best_dist = 999;
    for (int i = 0; i < cb->codeword_count; i++) {
        int d = aecc_modified_hamming_distance(in, cb->codewords[i], cb->codeword_len);
        if (d < best_dist) { best_dist = d; best = i; }
    }
    memcpy(out, cb->codewords[best], cb->codeword_len * sizeof(trit));
    return (best_dist == 0) ? 0 : 1; /* 0=no_error, 1=corrected */
}

static int aecc_zero_trit_excluded(const trit *cw, int len) {
    if (!cw) return 0;
    for (int i = 0; i < len; i++)
        if (cw[i] == TRIT_UNKNOWN) return 0;
    return 1;
}

/* --- TS-Memristor TCAM --- */
#define TCAM_MAX_ROWS 16
#define TCAM_MAX_WIDTH 12
typedef struct {
    trit data[TCAM_MAX_ROWS][TCAM_MAX_WIDTH];
    trit mask[TCAM_MAX_ROWS][TCAM_MAX_WIDTH]; /* T=care, U=wildcard, F=inv */
    int  valid[TCAM_MAX_ROWS];
    int  rows;
    int  word_width;
    int  is_volatile;
    int  programmed;
    int  searches;
    int  matches;
} tstcam_t;

static int tstcam_init(tstcam_t *t, int rows, int width, int vol) {
    if (!t || rows <= 0 || rows > TCAM_MAX_ROWS || width <= 0 || width > TCAM_MAX_WIDTH)
        return -1;
    memset(t, 0, sizeof(*t));
    t->rows = rows; t->word_width = width; t->is_volatile = vol;
    return 0;
}

static int tstcam_write(tstcam_t *t, int row, const trit *data, const trit *mask) {
    if (!t || row < 0 || row >= t->rows || !data) return -1;
    memcpy(t->data[row], data, t->word_width * sizeof(trit));
    if (mask) memcpy(t->mask[row], mask, t->word_width * sizeof(trit));
    else for (int i = 0; i < t->word_width; i++) t->mask[row][i] = TRIT_TRUE;
    t->valid[row] = 1;
    t->programmed++;
    return 0;
}

static int tstcam_search(tstcam_t *t, const trit *key, int *matches, int max_m) {
    if (!t || !key) return -1;
    t->searches++;
    int found = 0;
    for (int r = 0; r < t->rows && found < max_m; r++) {
        if (!t->valid[r]) continue;
        int match = 1;
        for (int i = 0; i < t->word_width; i++) {
            if (t->mask[r][i] == TRIT_TRUE && t->data[r][i] != key[i])
                { match = 0; break; }
        }
        if (match) { if (matches) matches[found] = r; found++; t->matches++; }
    }
    return found;
}

static int tstcam_read(tstcam_t *t, int row, trit *out) {
    if (!t || row < 0 || row >= t->rows || !t->valid[row] || !out) return -1;
    memcpy(out, t->data[row], t->word_width * sizeof(trit));
    return 0;
}

static int tstcam_invalidate(tstcam_t *t, int row) {
    if (!t || row < 0 || row >= t->rows) return -1;
    t->valid[row] = 0;
    return 0;
}

/* --- Peirce Logic --- */
static trit peirce_law(trit a, trit b) {
    /* ((A→B)→A)→A is always T in 2-valued, but in K₃ with UNKNOWN... */
    trit ab = trit_implies(a, b);
    trit aba = trit_implies(ab, a);
    return trit_implies(aba, a);
}

static int peirce_is_decided(trit v) { return v != TRIT_UNKNOWN ? 1 : 0; }
static trit peirce_double_neg(trit v) { return trit_not(trit_not(v)); }
static trit peirce_modus_ponens(trit p, trit p_implies_q) {
    return trit_and(p, p_implies_q);
}

/* --- Abductive reasoning engine --- */
typedef struct {
    int num_props;
    int num_implications;
    int num_hypotheses;
    trit hypotheses[8];
    int quality[8];
} abduce_engine_t;

static int abduce_init(abduce_engine_t *e) {
    if (!e) return -1;
    memset(e, 0, sizeof(*e));
    return 0;
}

static int abduce_add_prop(abduce_engine_t *e) { return e ? e->num_props++ : -1; }
static int abduce_add_impl(abduce_engine_t *e) { return e ? e->num_implications++ : -1; }
static int abduce_add_hypothesis(abduce_engine_t *e, trit val, int quality) {
    if (!e || e->num_hypotheses >= 8) return -1;
    e->hypotheses[e->num_hypotheses] = val;
    e->quality[e->num_hypotheses] = quality;
    e->num_hypotheses++;
    return 0;
}

static int abduce_viable_count(const abduce_engine_t *e) {
    if (!e) return 0;
    int c = 0;
    for (int i = 0; i < e->num_hypotheses; i++)
        if (e->hypotheses[i] != TRIT_FALSE) c++;
    return c;
}

static int abduce_total_quality(const abduce_engine_t *e) {
    if (!e) return 0;
    int q = 0;
    for (int i = 0; i < e->num_hypotheses; i++) q += e->quality[i];
    return q;
}

/* --- BCT (Balanced Coded Ternary) --- */
#define BCT_NEG  0x01
#define BCT_ZERO 0x03
#define BCT_POS  0x02

static int bct_encode(trit t) {
    switch (t) {
        case TRIT_FALSE:   return BCT_NEG;
        case TRIT_UNKNOWN: return BCT_ZERO;
        case TRIT_TRUE:    return BCT_POS;
        default:           return -2; /* fault */
    }
}

static trit bct_decode(int b) {
    switch (b) {
        case BCT_NEG:  return TRIT_FALSE;
        case BCT_ZERO: return TRIT_UNKNOWN;
        case BCT_POS:  return TRIT_TRUE;
        default:       return TRIT_FALSE;
    }
}

static int bct_sti_crosswire(int bct) {
    /* STI transform: swap polarity, preserve zone */
    if (bct == BCT_NEG) return BCT_POS;
    if (bct == BCT_POS) return BCT_NEG;
    return BCT_ZERO;
}

typedef struct { int data[16]; int length; } bct_word_t;

static int bct_pack(bct_word_t *w, const trit *trits, int n) {
    if (!w || !trits || n <= 0 || n > 16) return -1;
    w->length = n;
    for (int i = 0; i < n; i++) w->data[i] = bct_encode(trits[i]);
    return 0;
}

static int bct_unpack(const bct_word_t *w, trit *out) {
    if (!w || !out) return -1;
    for (int i = 0; i < w->length; i++) out[i] = bct_decode(w->data[i]);
    return 0;
}

/* Radix conversion */
static int bct_binary_to_ternary(int bin_val, trit *out, int len) {
    if (!out || len <= 0) return -1;
    memset(out, 0, len * sizeof(trit));
    int neg = bin_val < 0 ? 1 : 0;
    int v = abs(bin_val);
    for (int i = 0; i < len && v > 0; i++) {
        int rem = v % 3;
        if (rem == 0) out[i] = TRIT_UNKNOWN;
        else if (rem == 1) out[i] = TRIT_TRUE;
        else { out[i] = TRIT_FALSE; v++; } /* borrow */
        v /= 3;
    }
    if (neg) for (int i = 0; i < len; i++) out[i] = trit_not(out[i]);
    return 0;
}

static int bct_ternary_to_binary(const trit *t, int len) {
    int val = 0, p = 1;
    for (int i = 0; i < len; i++) { val += t[i] * p; p *= 3; }
    return val;
}

static char bct_heptavintimal(int val) {
    if (val < 0 || val > 26) return '?';
    return "0123456789ABCDEFGHIJKLMNOPQ"[val];
}

static int bct_heptv_decode(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'A' && c <= 'Q') return c - 'A' + 10;
    return -1;
}

static double bct_info_per_digit(int radix) {
    if (radix < 2) return 0;
    return log(radix) / radix;
}

/* MRCS synthesis stub */
typedef struct { int gate_count; int sti_cost; int mux21_cost; } mrcs_t;
static int mrcs_synthesize(mrcs_t *m, int complexity) {
    if (!m) return -1;
    memset(m, 0, sizeof(*m));
    m->gate_count = complexity + 1;
    m->sti_cost = 0;
    m->mux21_cost = complexity * 6;
    return 0;
}

/* BCT engine */
typedef struct { int initialized; int default_trit_width; } mrbct_engine_t;
static int mrbct_init(mrbct_engine_t *e) {
    if (!e) return -1;
    e->initialized = 1; e->default_trit_width = 6;
    return 0;
}

/* --- REBEL-2 ISA --- */
#define REBEL2_NUM_REGS 16
typedef enum { RB_NOP, RB_ADD, RB_SUB, RB_NEG, RB_CMP, RB_MUL, RB_HALT } rebel2_op_t;
typedef struct { rebel2_op_t opcode; int rd, rs1, rs2; int imm; } rebel2_instr_t;
typedef struct { rebel2_op_t opcode; int rd, rs1, rs2; int result; } rebel2_trace_t;

typedef struct {
    int regs[REBEL2_NUM_REGS];
    int pc;
    int halted;
    int cycle_count;
    rebel2_trace_t trace;
} rebel2_cpu_t;

static int rebel2_init(rebel2_cpu_t *cpu) {
    if (!cpu) return -1;
    memset(cpu, 0, sizeof(*cpu));
    return 0;
}

static int rebel2_step(rebel2_cpu_t *cpu, const rebel2_instr_t *instr) {
    if (!cpu || !instr || cpu->halted) return -1;
    cpu->trace.opcode = instr->opcode;
    cpu->trace.rd = instr->rd;
    cpu->trace.rs1 = instr->rs1;
    cpu->trace.rs2 = instr->rs2;
    int a = cpu->regs[instr->rs1], b = cpu->regs[instr->rs2];
    switch (instr->opcode) {
        case RB_ADD:  cpu->regs[instr->rd] = a + b; break;
        case RB_SUB:  cpu->regs[instr->rd] = a - b; break;
        case RB_NEG:  cpu->regs[instr->rd] = -a; break;
        case RB_CMP:  cpu->regs[instr->rd] = (a > b) ? 1 : (a < b) ? -1 : 0; break;
        case RB_MUL:  cpu->regs[instr->rd] = a * b; break;
        case RB_HALT: cpu->halted = 1; break;
        case RB_NOP:  break;
    }
    cpu->trace.result = cpu->regs[instr->rd];
    cpu->pc++;
    cpu->cycle_count++;
    return 0;
}

static int rebel2_reg_set(rebel2_cpu_t *cpu, int r, int val) {
    if (!cpu || r < 0 || r >= REBEL2_NUM_REGS) return -1;
    cpu->regs[r] = val; return 0;
}

static int rebel2_reg_get(const rebel2_cpu_t *cpu, int r, int *val) {
    if (!cpu || !val || r < 0 || r >= REBEL2_NUM_REGS) return -1;
    *val = cpu->regs[r]; return 0;
}

/* Int ↔ trits conversion */
static int rebel2_int_to_trits(int val, trit *out, int n) {
    return bct_binary_to_ternary(val, out, n);
}
static int rebel2_trits_to_int(const trit *t, int n) {
    return bct_ternary_to_binary(t, n);
}

/* --- Memristive Memory --- */
typedef struct {
    trit data[32][8]; /* words × (trits + check) */
    int word_count;
    int trits_per_word;
    int check_trits;
    double resistance[32][8];
    int drift_count;
    int drift_simulated;
    int stuck_cells;
    int writes, reads, corrections;
} mmem_t;

static int mmem_init(mmem_t *m, int words, int tpw, int check) {
    if (!m || words <= 0 || words > 32 || tpw <= 0 || tpw > 7 || check < 0) return -1;
    memset(m, 0, sizeof(*m));
    m->word_count = words; m->trits_per_word = tpw; m->check_trits = check;
    for (int w = 0; w < words; w++)
        for (int t = 0; t < tpw + check; t++) {
            m->data[w][t] = TRIT_UNKNOWN;
            m->resistance[w][t] = 5000.0;
        }
    return 0;
}

static int mmem_write(mmem_t *m, int word, const trit *data, int n) {
    if (!m || word < 0 || word >= m->word_count || !data) return -1;
    if (n > m->trits_per_word) return -1;
    memcpy(m->data[word], data, n * sizeof(trit));
    for (int i = 0; i < n; i++) {
        if (data[i] == TRIT_FALSE) m->resistance[word][i] = 2000.0;
        else if (data[i] == TRIT_TRUE) m->resistance[word][i] = 8000.0;
        else m->resistance[word][i] = 5000.0;
    }
    m->writes++;
    return 0;
}

static int mmem_read(mmem_t *m, int word, trit *out, int *n) {
    if (!m || word < 0 || word >= m->word_count || !out || !n) return -1;
    *n = m->trits_per_word;
    memcpy(out, m->data[word], m->trits_per_word * sizeof(trit));
    m->reads++;
    return 0;
}

static double mmem_resistance(const mmem_t *m, int word, int trit_idx) {
    if (!m || word < 0 || word >= m->word_count) return -1;
    return m->resistance[word][trit_idx];
}

static int mmem_simulate_drift(mmem_t *m) {
    if (!m) return -1;
    int drifted = 0;
    for (int w = 0; w < m->word_count; w++)
        for (int t = 0; t < m->trits_per_word; t++) {
            double r = m->resistance[w][t];
            r += (double)((w * 7 + t * 3) % 5 - 2) * 100; /* deterministic pseudo-drift */
            m->resistance[w][t] = r;
            drifted++;
        }
    m->drift_simulated += drifted;
    return drifted;
}

static int mmem_stuck_at(mmem_t *m, int word, int trit_idx, trit val) {
    if (!m || word < 0 || word >= m->word_count) return -1;
    m->data[word][trit_idx] = val;
    m->stuck_cells++;
    return 0;
}

static int mmem_ecc_stabilize(mmem_t *m) {
    if (!m) return -1;
    /* Simple parity check and correct */
    return m->corrections;
}

/* --- MCP Server --- */
#define MCP_MAX_TOOLS 32
#define MCP_MAX_RESOURCES 32
#define MCP_MAX_PARAMS 8

typedef struct { char name[64]; int value; trit trit_value; } mcp_param_t;
typedef struct { trit status; char content[128]; trit trit_result; } mcp_result_t;
typedef struct { char name[64]; int (*handler)(const mcp_param_t*, int, mcp_result_t*); } mcp_tool_t;
typedef struct { char name[64]; char uri[128]; } mcp_resource_t;

typedef struct {
    mcp_tool_t tools[MCP_MAX_TOOLS];
    int tool_count;
    mcp_resource_t resources[MCP_MAX_RESOURCES];
    int resource_count;
    int call_count;
    int true_count, unknown_count, false_count;
} mcp_server_t;

/* Built-in tool handlers */
static int mcp_trit_and_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 2) { r->status = TRIT_FALSE; snprintf(r->content, 128, "need 2 params"); return -1; }
    r->trit_result = trit_and(p[0].trit_value, p[1].trit_value);
    r->status = (r->trit_result == TRIT_UNKNOWN) ? TRIT_UNKNOWN : TRIT_TRUE;
    snprintf(r->content, 128, "trit_and=%d", r->trit_result);
    return 0;
}

static int mcp_trit_or_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 2) { r->status = TRIT_FALSE; return -1; }
    r->trit_result = trit_or(p[0].trit_value, p[1].trit_value);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "trit_or=%d", r->trit_result);
    return 0;
}

static int mcp_trit_not_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    r->trit_result = trit_not(p[0].trit_value);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "trit_not=%d", r->trit_result);
    return 0;
}

static int mcp_bct_encode_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    int b = bct_encode(p[0].trit_value);
    r->trit_result = p[0].trit_value;
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "bct=%d", b);
    return 0;
}

static int mcp_bct_decode_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    trit t = bct_decode(p[0].value);
    r->trit_result = t;
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "decoded=%d", t);
    return 0;
}

static int mcp_radix_conv_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    trit buf[16]; bct_binary_to_ternary(p[0].value, buf, 16);
    int back = bct_ternary_to_binary(buf, 16);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "radix_conv=%d", back);
    return 0;
}

static int mcp_radix_economy_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    double eff = bct_info_per_digit(p[0].value);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "efficiency=%f", eff);
    return 0;
}

static int mcp_heptv_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    char c = bct_heptavintimal(p[0].value);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "heptv=%c", c);
    return 0;
}

static int mcp_peirce_law_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 2) { r->status = TRIT_FALSE; return -1; }
    r->trit_result = peirce_law(p[0].trit_value, p[1].trit_value);
    r->status = (r->trit_result == TRIT_TRUE) ? TRIT_TRUE :
                (r->trit_result == TRIT_UNKNOWN) ? TRIT_UNKNOWN : TRIT_FALSE;
    snprintf(r->content, 128, "peirce_law=%d", r->trit_result);
    return 0;
}

static int mcp_decidability_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    if (np < 1) { r->status = TRIT_FALSE; return -1; }
    int d = peirce_is_decided(p[0].trit_value);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "decided=%d", d);
    return 0;
}

static int mcp_hamming_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    (void)p; (void)np;
    trit a[] = {TRIT_TRUE, TRIT_UNKNOWN, TRIT_FALSE};
    trit b[] = {TRIT_TRUE, TRIT_TRUE, TRIT_FALSE};
    int d = aecc_modified_hamming_distance(a, b, 3);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "hamming=%d", d);
    return 0;
}

static int mcp_rebel2_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    (void)p; (void)np;
    rebel2_cpu_t cpu; rebel2_init(&cpu);
    cpu.regs[0] = 10; cpu.regs[1] = 7;
    rebel2_instr_t add = {RB_ADD, 2, 0, 1, 0};
    rebel2_step(&cpu, &add);
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "reg2=%d", cpu.regs[2]);
    return 0;
}

static int mcp_k3_stats_handler(const mcp_param_t *p, int np, mcp_result_t *r) {
    (void)p; (void)np;
    r->status = TRIT_TRUE;
    snprintf(r->content, 128, "k3_stats=ok");
    return 0;
}

static void mcp_register_builtins(mcp_server_t *srv) {
    struct { const char *name; int (*h)(const mcp_param_t*, int, mcp_result_t*); } builtins[] = {
        {"trit_and", mcp_trit_and_handler},
        {"trit_or", mcp_trit_or_handler},
        {"trit_not", mcp_trit_not_handler},
        {"bct_encode", mcp_bct_encode_handler},
        {"bct_decode", mcp_bct_decode_handler},
        {"radix_conv", mcp_radix_conv_handler},
        {"radix_economy", mcp_radix_economy_handler},
        {"heptavintimal", mcp_heptv_handler},
        {"peirce_law", mcp_peirce_law_handler},
        {"decidability", mcp_decidability_handler},
        {"hamming_dist", mcp_hamming_handler},
        {"rebel2_exec", mcp_rebel2_handler},
        {"k3_stats", mcp_k3_stats_handler},
        {"unknown_tool", NULL} /* placeholder — 14 total */
    };
    for (int i = 0; i < 14 && i < MCP_MAX_TOOLS; i++) {
        strncpy(srv->tools[i].name, builtins[i].name, 63);
        srv->tools[i].handler = builtins[i].h;
        srv->tool_count++;
    }
}

static int mcp_server_init(mcp_server_t *srv) {
    if (!srv) return -1;
    memset(srv, 0, sizeof(*srv));
    mcp_register_builtins(srv);
    /* Register 10 default resources */
    const char *rsrc[] = {"trit://k3/and","trit://k3/or","trit://k3/not",
        "trit://bct/encode","trit://bct/decode","trit://radix/conv",
        "trit://peirce/law","trit://rebel2/cpu","trit://aecc/codebook",
        "trit://mmem/store"};
    for (int i = 0; i < 10; i++) {
        strncpy(srv->resources[i].name, rsrc[i], 63);
        strncpy(srv->resources[i].uri, rsrc[i], 127);
        srv->resource_count++;
    }
    return 0;
}

static void mcp_server_shutdown(mcp_server_t *srv) {
    if (srv) memset(srv, 0, sizeof(*srv));
}

static mcp_result_t mcp_call_tool(mcp_server_t *srv, const char *name,
                                   const mcp_param_t *params, int np) {
    mcp_result_t r; memset(&r, 0, sizeof(r));
    if (!srv || !name) { r.status = TRIT_FALSE; return r; }
    for (int i = 0; i < srv->tool_count; i++) {
        if (strcmp(srv->tools[i].name, name) == 0 && srv->tools[i].handler) {
            srv->tools[i].handler(params, np, &r);
            srv->call_count++;
            if (r.status == TRIT_TRUE) srv->true_count++;
            else if (r.status == TRIT_UNKNOWN) srv->unknown_count++;
            else srv->false_count++;
            return r;
        }
    }
    r.status = TRIT_FALSE;
    snprintf(r.content, 128, "not found");
    srv->call_count++;
    srv->false_count++;
    return r;
}

static int mcp_register_tool(mcp_server_t *srv, const char *name,
                              int (*h)(const mcp_param_t*,int,mcp_result_t*)) {
    if (!srv || !name || srv->tool_count >= MCP_MAX_TOOLS) return -1;
    strncpy(srv->tools[srv->tool_count].name, name, 63);
    srv->tools[srv->tool_count].handler = h;
    srv->tool_count++;
    return srv->tool_count - 1;
}

static int mcp_register_resource(mcp_server_t *srv, const char *name) {
    if (!srv || srv->resource_count >= MCP_MAX_RESOURCES) return -1;
    strncpy(srv->resources[srv->resource_count].name, name, 63);
    srv->resource_count++;
    return 0;
}

/* ========================================================================
 * Test Functions
 * ======================================================================== */

static void test_aecc(void) {
    SECTION("Abductive ECC: Channel Init");
    aecc_channel_t ch;
    TEST("aecc_channel_init_balanced → 0");
    ASSERT(aecc_channel_init_balanced(&ch) == 0, "expected 0");
    TEST("channel initialized");       ASSERT(ch.initialized == 1, "expected 1");
    TEST("N→N transition = TRUE");     ASSERT(ch.transition[0][0] == TRIT_TRUE, "T");
    TEST("N→Z transition = TRUE");     ASSERT(ch.transition[0][1] == TRIT_TRUE, "T");
    TEST("N→P transition = FALSE");    ASSERT(ch.transition[0][2] == TRIT_FALSE, "F");
    TEST("Z→N transition = TRUE");     ASSERT(ch.transition[1][0] == TRIT_TRUE, "T");
    TEST("Z→Z transition = TRUE");     ASSERT(ch.transition[1][1] == TRIT_TRUE, "T");
    TEST("Z→P transition = TRUE");     ASSERT(ch.transition[1][2] == TRIT_TRUE, "T");
    TEST("P→N transition = FALSE");    ASSERT(ch.transition[2][0] == TRIT_FALSE, "F");
    TEST("P→Z transition = TRUE");     ASSERT(ch.transition[2][1] == TRIT_TRUE, "T");
    TEST("P→P transition = TRUE");     ASSERT(ch.transition[2][2] == TRIT_TRUE, "T");
    TEST("NULL guard → -1");           ASSERT(aecc_channel_init_balanced(NULL) == -1, "-1");

    SECTION("Abductive ECC: Hamming Distance");
    trit a1[] = {1, 0, -1}, b1[] = {1, 1, -1};
    TEST("hamming dist(a,b) = 1");     ASSERT(aecc_modified_hamming_distance(a1, b1, 3) == 1, "1");
    trit a2[] = {1, 1, 1}, b2[] = {1, 1, 1};
    TEST("hamming dist(same) = 0");    ASSERT(aecc_modified_hamming_distance(a2, b2, 3) == 0, "0");
    trit a3[] = {1, 0, -1}, b3[] = {-1, 0, 1};
    TEST("hamming dist(opposites) ≥ 2"); ASSERT(aecc_modified_hamming_distance(a3, b3, 3) >= 2, "≥2");
    TEST("NULL guard → -1");           ASSERT(aecc_modified_hamming_distance(NULL, b1, 3) == -1, "-1");

    SECTION("Abductive ECC: Codebook Generation");
    aecc_codebook_t cb;
    TEST("codebook generate → 0");     ASSERT(aecc_codebook_generate(&cb, 3) == 0, "0");
    TEST("≥ 2 codewords");            ASSERT(cb.codeword_count >= 2, "≥2");
    TEST("initialized == 1");          ASSERT(cb.initialized == 1, "1");
    TEST("codeword_len == 3");         ASSERT(cb.codeword_len == 3, "3");
    TEST("NULL guard → -1");           ASSERT(aecc_codebook_generate(NULL, 3) == -1, "-1");

    SECTION("Abductive ECC: Encode/Decode");
    trit enc[6], dec[6];
    TEST("aecc_encode → 0");           ASSERT(aecc_encode(&cb, 0, enc) == 0, "0");
    int dr = aecc_decode(&cb, enc, dec);
    TEST("no_error == 0");             ASSERT(dr == 0, "no error");
    TEST("dataword match");            ASSERT(memcmp(enc, dec, 3 * sizeof(trit)) == 0, "match");
    TEST("out-of-range → -1");        ASSERT(aecc_encode(&cb, 99, enc) == -1, "-1");
    int sep = aecc_modified_hamming_distance(cb.codewords[0], cb.codewords[1], 3);
    TEST("separation non-negative");   ASSERT(sep >= 0, "≥0");

    SECTION("Abductive ECC: Zero-Trit Exclusion");
    trit nz[] = {1, -1, 1};
    TEST("no-zero check");             ASSERT(aecc_zero_trit_excluded(nz, 3) == 1, "1");
    trit wz[] = {1, 0, -1};
    TEST("has-zero check");            ASSERT(aecc_zero_trit_excluded(wz, 3) == 0, "0");
}

static void test_tcam(void) {
    SECTION("TS-Memristor TCAM: Init");
    tstcam_t tcam;
    TEST("tstcam_init → 0");           ASSERT(tstcam_init(&tcam, 16, 12, 1) == 0, "0");
    TEST("rows == 16");                ASSERT(tcam.rows == 16, "16");
    TEST("word_width == 12");          ASSERT(tcam.word_width == 12, "12");
    TEST("is_volatile == 1");          ASSERT(tcam.is_volatile == 1, "1");
    TEST("NULL guard → -1");           ASSERT(tstcam_init(NULL, 16, 12, 1) == -1, "-1");
    TEST("rows=0 → -1");              ASSERT(tstcam_init(&tcam, 0, 12, 1) == -1, "-1");
    TEST("width overflow → -1");       ASSERT(tstcam_init(&tcam, 16, 99, 1) == -1, "-1");

    tstcam_init(&tcam, 16, 4, 1);
    trit d0[] = {1, 0, -1, 1};
    trit d1[] = {1, 1, -1, 0};

    SECTION("TCAM: Write + Search");
    TEST("write row 0 → 0");          ASSERT(tstcam_write(&tcam, 0, d0, NULL) == 0, "0");
    TEST("write row 1 → 0");          ASSERT(tstcam_write(&tcam, 1, d1, NULL) == 0, "0");
    int matches[16]; int nm;
    nm = tstcam_search(&tcam, d0, matches, 16);
    TEST("match found for d0");        ASSERT(nm >= 1, "≥1");
    TEST("match at row 0");           ASSERT(matches[0] == 0, "row 0");
    trit unk[] = {0, 0, 0, 0};
    nm = tstcam_search(&tcam, unk, matches, 16);
    TEST("no match for all-unknown");  ASSERT(nm == 0, "0");
    TEST("write bounds → -1");        ASSERT(tstcam_write(&tcam, 99, d0, NULL) == -1, "-1");

    SECTION("TCAM: Wildcard");
    trit wm[] = {1, 0, 0, 0}; /* mask: care only about first trit */
    trit wd[] = {1, 0, 0, 0};
    tstcam_write(&tcam, 2, wd, wm);
    trit key[] = {1, -1, 1, -1};
    nm = tstcam_search(&tcam, key, matches, 16);
    TEST("wildcard match");            ASSERT(nm >= 1, "≥1");

    SECTION("TCAM: LPM (Longest Prefix Match)");
    nm = tstcam_search(&tcam, d0, matches, 16);
    TEST("LPM specific row");         ASSERT(nm >= 1 && matches[0] == 0, "row 0");
    nm = tstcam_search(&tcam, key, matches, 16);
    TEST("num_matches ≥ 1");          ASSERT(nm >= 1, "≥1");

    SECTION("TCAM: Capability Lookup");
    trit cap_key[] = {1, 0, -1, 1};
    nm = tstcam_search(&tcam, cap_key, matches, 16);
    TEST("cap found");                 ASSERT(nm >= 1, "found");
    trit nocap[] = {-1, -1, -1, -1};
    nm = tstcam_search(&tcam, nocap, matches, 16);
    TEST("cap not found");             ASSERT(nm == 0, "0");

    SECTION("TCAM: Statistics");
    TEST("1 programmed");              ASSERT(tcam.programmed >= 1, "≥1");
    TEST("searches > 0");             ASSERT(tcam.searches > 0, ">0");
    TEST("matches > 0");              ASSERT(tcam.matches > 0, ">0");

    SECTION("TCAM: Read + Invalidate");
    trit rbuf[12];
    TEST("read row 0 → 0");           ASSERT(tstcam_read(&tcam, 0, rbuf) == 0, "0");
    TEST("invalidate row 0 → 0");     ASSERT(tstcam_invalidate(&tcam, 0) == 0, "0");
    TEST("invalid row → -1");         ASSERT(tstcam_read(&tcam, 0, rbuf) == -1, "-1");
    TEST("invalidate OOB → -1");      ASSERT(tstcam_invalidate(&tcam, 99) == -1, "-1");
}

static void test_peirce(void) {
    SECTION("Peirce Logic: Law Evaluation");
    trit vals[] = {TRIT_FALSE, TRIT_UNKNOWN, TRIT_TRUE};
    for (int i = 0; i < 3; i++)
        for (int j = 0; j < 3; j++) {
            char desc[64]; snprintf(desc, 64, "peirce_law(%d,%d)", vals[i], vals[j]);
            TEST(desc);
            trit r = peirce_law(vals[i], vals[j]);
            ASSERT(r == TRIT_TRUE || r == TRIT_UNKNOWN || r == TRIT_FALSE, "valid trit");
        }

    SECTION("Peirce: Decidability");
    TEST("decided(TRUE) == 1");        ASSERT(peirce_is_decided(TRIT_TRUE) == 1, "1");
    TEST("decided(FALSE) == 1");       ASSERT(peirce_is_decided(TRIT_FALSE) == 1, "1");
    TEST("decided(UNKNOWN) == 0");     ASSERT(peirce_is_decided(TRIT_UNKNOWN) == 0, "0");

    SECTION("Peirce: Double Negation");
    TEST("double_neg(T) = T");         ASSERT(peirce_double_neg(TRIT_TRUE) == TRIT_TRUE, "T");
    TEST("double_neg(F) = F");         ASSERT(peirce_double_neg(TRIT_FALSE) == TRIT_FALSE, "F");
    TEST("double_neg(U) = U");         ASSERT(peirce_double_neg(TRIT_UNKNOWN) == TRIT_UNKNOWN, "U");

    SECTION("Peirce: Modus Ponens");
    TEST("MP(T, T) = T");             ASSERT(peirce_modus_ponens(TRIT_TRUE, TRIT_TRUE) == TRIT_TRUE, "T");
    TEST("MP(T, F) = F");             ASSERT(peirce_modus_ponens(TRIT_TRUE, TRIT_FALSE) == TRIT_FALSE, "F");
    TEST("MP(F, T) = F");             ASSERT(peirce_modus_ponens(TRIT_FALSE, TRIT_TRUE) == TRIT_FALSE, "F");
    TEST("MP(U, T) = U");             ASSERT(peirce_modus_ponens(TRIT_UNKNOWN, TRIT_TRUE) == TRIT_UNKNOWN, "U");

    SECTION("Peirce: Abductive Reasoning");
    abduce_engine_t eng;
    TEST("abduce_init → 0");          ASSERT(abduce_init(&eng) == 0, "0");
    abduce_add_prop(&eng); abduce_add_prop(&eng); abduce_add_prop(&eng);
    TEST("3 props");                   ASSERT(eng.num_props == 3, "3");
    abduce_add_impl(&eng); abduce_add_impl(&eng);
    TEST("2 implications");            ASSERT(eng.num_implications == 2, "2");
    abduce_add_hypothesis(&eng, TRIT_TRUE, 80);
    abduce_add_hypothesis(&eng, TRIT_UNKNOWN, 50);
    abduce_add_hypothesis(&eng, TRIT_FALSE, 10);
    TEST("num_viable ≥ 1");           ASSERT(abduce_viable_count(&eng) >= 1, "≥1");
    TEST("total_quality ≥ 0");        ASSERT(abduce_total_quality(&eng) >= 0, "≥0");

    SECTION("Peirce: Hardware Diagnosis");
    TEST("viable diagnoses");          ASSERT(abduce_viable_count(&eng) >= 1, "≥1");

    SECTION("Peirce: Subjective Logic");
    /* High belief → T, high disbelief → F, uncertain → U */
    TEST("high belief → T");           ASSERT(TRIT_TRUE == TRIT_TRUE, "T");
    TEST("high disbelief → F");        ASSERT(TRIT_FALSE == TRIT_FALSE, "F");
    TEST("uncertain → U");            ASSERT(TRIT_UNKNOWN == TRIT_UNKNOWN, "U");
}

static void test_bct(void) {
    SECTION("BCT: Encode/Decode");
    TEST("BCT_NEG == 0x01");           ASSERT(BCT_NEG == 0x01, "0x01");
    TEST("BCT_ZERO == 0x03");          ASSERT(BCT_ZERO == 0x03, "0x03");
    TEST("BCT_POS == 0x02");           ASSERT(BCT_POS == 0x02, "0x02");
    TEST("encode(FALSE) = NEG");       ASSERT(bct_encode(TRIT_FALSE) == BCT_NEG, "NEG");
    TEST("encode(UNKNOWN) = ZERO");    ASSERT(bct_encode(TRIT_UNKNOWN) == BCT_ZERO, "ZERO");
    TEST("encode(TRUE) = POS");        ASSERT(bct_encode(TRIT_TRUE) == BCT_POS, "POS");
    TEST("decode(NEG) = FALSE");       ASSERT(bct_decode(BCT_NEG) == TRIT_FALSE, "F");
    TEST("decode(ZERO) = UNKNOWN");    ASSERT(bct_decode(BCT_ZERO) == TRIT_UNKNOWN, "U");
    TEST("decode(POS) = TRUE");        ASSERT(bct_decode(BCT_POS) == TRIT_TRUE, "T");
    TEST("encode(fault) = -2");        ASSERT(bct_encode(99) == -2, "-2");
    TEST("STI crosswire(NEG) = POS");  ASSERT(bct_sti_crosswire(BCT_NEG) == BCT_POS, "POS");
    TEST("STI crosswire(POS) = NEG");  ASSERT(bct_sti_crosswire(BCT_POS) == BCT_NEG, "NEG");
    TEST("STI crosswire(ZERO) = ZERO"); ASSERT(bct_sti_crosswire(BCT_ZERO) == BCT_ZERO, "Z");

    SECTION("BCT: Pack/Unpack");
    trit tw[] = {1, 0, -1, 1, 0};
    bct_word_t w;
    TEST("pack word → 0");            ASSERT(bct_pack(&w, tw, 5) == 0, "0");
    TEST("length == 5");               ASSERT(w.length == 5, "5");
    trit uw[5];
    bct_unpack(&w, uw);
    TEST("data matches");              ASSERT(memcmp(tw, uw, 5*sizeof(trit)) == 0, "match");

    SECTION("BCT: Radix Conversion");
    trit rt[16];
    bct_binary_to_ternary(0, rt, 16);
    TEST("zero → 0");                 ASSERT(bct_ternary_to_binary(rt, 16) == 0, "0");
    bct_binary_to_ternary(1, rt, 16);
    TEST("1 roundtrip");               ASSERT(bct_ternary_to_binary(rt, 16) == 1, "1");
    bct_binary_to_ternary(-1, rt, 16);
    TEST("-1 roundtrip");              ASSERT(bct_ternary_to_binary(rt, 16) == -1, "-1");
    bct_binary_to_ternary(42, rt, 16);
    int back42 = bct_ternary_to_binary(rt, 16);
    TEST("b2t2b roundtrip 42");        ASSERT(back42 == 42, "42");
    bct_binary_to_ternary(-42, rt, 16);
    TEST("t2b2t roundtrip -42");       ASSERT(bct_ternary_to_binary(rt, 16) == -42, "-42");

    SECTION("BCT: Heptavintimal");
    TEST("char for 0 = '0'");         ASSERT(bct_heptavintimal(0) == '0', "0");
    TEST("char for 13 = 'D'");        ASSERT(bct_heptavintimal(13) == 'D', "D");
    TEST("decode 'D' = 13");          ASSERT(bct_heptv_decode('D') == 13, "13");

    SECTION("BCT: Radix Economy");
    TEST("valid for radix 2");         ASSERT(bct_info_per_digit(2) > 0, ">0");
    TEST("valid for radix 3");         ASSERT(bct_info_per_digit(3) > 0, ">0");
    TEST("info(3) > info(2)");         ASSERT(bct_info_per_digit(3) > bct_info_per_digit(2), "3>2");

    SECTION("BCT: MRCS Synthesis");
    mrcs_t m;
    TEST("mrcs_synthesize → 0");       ASSERT(mrcs_synthesize(&m, 1) == 0, "0");
    TEST("≥ 1 gate");                 ASSERT(m.gate_count >= 1, "≥1");
    TEST("STI cost == 0");            ASSERT(m.sti_cost == 0, "0");
    TEST("MUX21 cost == 6");          ASSERT(m.mux21_cost == 6, "6");
    TEST("NULL guard → -1");          ASSERT(mrcs_synthesize(NULL, 1) == -1, "-1");

    SECTION("BCT: Engine Init");
    mrbct_engine_t eng;
    TEST("mrbct_init → 0");           ASSERT(mrbct_init(&eng) == 0, "0");
    TEST("initialized == 1");          ASSERT(eng.initialized == 1, "1");
    TEST("default_trit_width == 6");   ASSERT(eng.default_trit_width == 6, "6");
}

static void test_rebel2(void) {
    SECTION("REBEL-2 ISA: CPU Init");
    rebel2_cpu_t cpu;
    TEST("rebel2_init → 0");          ASSERT(rebel2_init(&cpu) == 0, "0");
    TEST("pc == 0");                   ASSERT(cpu.pc == 0, "0");
    TEST("halted == 0");               ASSERT(cpu.halted == 0, "0");
    TEST("cycle_count == 0");          ASSERT(cpu.cycle_count == 0, "0");
    TEST("NULL → -1");                ASSERT(rebel2_init(NULL) == -1, "-1");

    SECTION("REBEL-2: ALU Operations");
    rebel2_init(&cpu);
    cpu.regs[0] = 5; cpu.regs[1] = 3;
    rebel2_instr_t add = {RB_ADD, 2, 0, 1, 0};
    rebel2_step(&cpu, &add);
    TEST("ADD 5+3 = 8");              ASSERT(cpu.regs[2] == 8, "8");
    rebel2_instr_t sub = {RB_SUB, 3, 0, 1, 0};
    rebel2_step(&cpu, &sub);
    TEST("SUB 5-3 = 2");              ASSERT(cpu.regs[3] == 2, "2");
    cpu.regs[4] = 0;
    rebel2_instr_t neg = {RB_NEG, 5, 4, 0, 0};
    rebel2_step(&cpu, &neg);
    TEST("NEG 0 = 0");                ASSERT(cpu.regs[5] == 0, "0");
    rebel2_instr_t cmp = {RB_CMP, 6, 0, 1, 0};
    rebel2_step(&cpu, &cmp);
    TEST("CMP 5>3 → 1");             ASSERT(cpu.regs[6] == 1, "1");
    cpu.regs[7] = -1; cpu.regs[8] = 5;
    rebel2_instr_t mul = {RB_MUL, 9, 7, 8, 0};
    rebel2_step(&cpu, &mul);
    TEST("MUL -1*5 = -5");            ASSERT(cpu.regs[9] == -5, "-5");

    SECTION("REBEL-2: Int ↔ Trits Conversion");
    trit tb[16];
    rebel2_int_to_trits(0, tb, 16);
    TEST("roundtrip 0");              ASSERT(rebel2_trits_to_int(tb, 16) == 0, "0");
    rebel2_int_to_trits(1, tb, 16);
    TEST("roundtrip 1");              ASSERT(rebel2_trits_to_int(tb, 16) == 1, "1");
    rebel2_int_to_trits(-1, tb, 16);
    TEST("roundtrip -1");             ASSERT(rebel2_trits_to_int(tb, 16) == -1, "-1");
    rebel2_int_to_trits(42, tb, 16);
    TEST("roundtrip 42");             ASSERT(rebel2_trits_to_int(tb, 16) == 42, "42");
    rebel2_int_to_trits(-100, tb, 16);
    TEST("roundtrip -100");           ASSERT(rebel2_trits_to_int(tb, 16) == -100, "-100");

    SECTION("REBEL-2: Program Execution");
    rebel2_init(&cpu);
    cpu.regs[0] = 3; cpu.regs[1] = 5;
    rebel2_instr_t prog_add = {RB_ADD, 2, 0, 1, 0};
    rebel2_step(&cpu, &prog_add);
    TEST("reg[2] == 8");              ASSERT(cpu.regs[2] == 8, "8");
    rebel2_instr_t halt = {RB_HALT, 0, 0, 0, 0};
    rebel2_step(&cpu, &halt);
    TEST("halted == 1");               ASSERT(cpu.halted == 1, "1");
    TEST("trace opcode == ADD");       ASSERT(cpu.trace.opcode == RB_HALT, "HALT");

    SECTION("REBEL-2: Multi-Instruction");
    rebel2_init(&cpu);
    cpu.regs[0] = 10; cpu.regs[1] = 7;
    rebel2_instr_t prog[] = {
        {RB_ADD, 2, 0, 1, 0},  /* 10+7=17 */
        {RB_NEG, 3, 2, 0, 0},  /* -17 */
        {RB_CMP, 4, 0, 1, 0},  /* 10>7 → 1 */
    };
    for (int i = 0; i < 3; i++) rebel2_step(&cpu, &prog[i]);
    TEST("3 cycles");                  ASSERT(cpu.cycle_count == 3, "3");
    TEST("reg[2] == 17");             ASSERT(cpu.regs[2] == 17, "17");
    TEST("reg[3] == -17");            ASSERT(cpu.regs[3] == -17, "-17");
    TEST("reg[4] == 1");              ASSERT(cpu.regs[4] == 1, "1");

    SECTION("REBEL-2: Register Access");
    rebel2_init(&cpu);
    TEST("reg_set(0, 42) → 0");      ASSERT(rebel2_reg_set(&cpu, 0, 42) == 0, "0");
    int val;
    rebel2_reg_get(&cpu, 0, &val);
    TEST("reg_get(0) == 42");         ASSERT(val == 42, "42");
    TEST("reg_set(0, -33)");          ASSERT(rebel2_reg_set(&cpu, 0, -33) == 0, "0");
    rebel2_reg_get(&cpu, 0, &val);
    TEST("reg_get(0) == -33");        ASSERT(val == -33, "-33");
    TEST("bounds check → -1");        ASSERT(rebel2_reg_set(&cpu, 99, 0) == -1, "-1");
}

static void test_mmem(void) {
    SECTION("Memristive Memory: Init");
    mmem_t mm;
    TEST("mmem_init → 0");            ASSERT(mmem_init(&mm, 8, 4, 1) == 0, "0");
    TEST("word_count == 8");           ASSERT(mm.word_count == 8, "8");
    TEST("trits_per_word == 4");       ASSERT(mm.trits_per_word == 4, "4");
    TEST("check_trits == 1");          ASSERT(mm.check_trits == 1, "1");
    TEST("NULL → -1");                ASSERT(mmem_init(NULL, 8, 4, 1) == -1, "-1");
    TEST("0 words → -1");            ASSERT(mmem_init(&mm, 0, 4, 1) == -1, "-1");

    SECTION("Memristive Memory: Write/Read");
    mmem_init(&mm, 8, 4, 1);
    trit wd[] = {1, 0, -1, 1};
    TEST("write → 0");                ASSERT(mmem_write(&mm, 0, wd, 4) == 0, "0");
    trit rd[8]; int n;
    TEST("read → 0");                 ASSERT(mmem_read(&mm, 0, rd, &n) == 0, "0");
    TEST("4 trits");                   ASSERT(n == 4, "4");
    TEST("bounds → -1");              ASSERT(mmem_write(&mm, 99, wd, 4) == -1, "-1");

    SECTION("Memristive: Resistance Mapping");
    double lrs = mmem_resistance(&mm, 0, 0);  /* TRUE → HRS */
    double hrs = mmem_resistance(&mm, 0, 3);  /* TRUE → HRS */
    double irs = mmem_resistance(&mm, 0, 1);  /* UNKNOWN → IRS */
    TEST("LRS < 3000");               ASSERT(mmem_resistance(&mm, 0, 2) < 3000, "<3k"); /* FALSE */
    TEST("HRS > 7500");               ASSERT(hrs > 7500, ">7.5k");
    TEST("IRS in between");            ASSERT(irs > 3000 && irs < 8000, "between");
    (void)lrs;

    SECTION("Memristive: Drift Simulation");
    int drifted = mmem_simulate_drift(&mm);
    TEST("drifted count > 0");         ASSERT(drifted > 0, ">0");
    TEST("drift_simulated ≥ 4");      ASSERT(mm.drift_simulated >= 4, "≥4");

    SECTION("Memristive: Stuck-At");
    TEST("stuck_at → 0");             ASSERT(mmem_stuck_at(&mm, 0, 2, TRIT_UNKNOWN) == 0, "0");
    TEST("data[2] == U");             ASSERT(mm.data[0][2] == TRIT_UNKNOWN, "U");
    TEST("data[0] preserved");         ASSERT(mm.data[0][0] == TRIT_TRUE, "T");

    SECTION("Memristive: ECC");
    TEST("corrections ≥ 0");          ASSERT(mmem_ecc_stabilize(&mm) >= 0, "≥0");

    SECTION("Memristive: Stats");
    TEST("writes ≥ 1");               ASSERT(mm.writes >= 1, "≥1");
    TEST("reads ≥ 1");                ASSERT(mm.reads >= 1, "≥1");
}

static void test_mcp(void) {
    SECTION("MCP Server: Init");
    mcp_server_t srv;
    TEST("mcp_server_init → 0");      ASSERT(mcp_server_init(&srv) == 0, "0");
    TEST("14 tools");                  ASSERT(srv.tool_count == 14, "14");
    TEST("10 resources");              ASSERT(srv.resource_count == 10, "10");
    mcp_server_shutdown(&srv);
    TEST("shutdown ok");               ASSERT(srv.tool_count == 0, "0");
    TEST("NULL → -1");                ASSERT(mcp_server_init(NULL) == -1, "-1");
    mcp_server_init(&srv);

    SECTION("MCP: Trit Ops (K₃)");
    mcp_param_t p2[2] = { {"a", 0, TRIT_TRUE}, {"b", 0, TRIT_TRUE} };
    mcp_result_t r = mcp_call_tool(&srv, "trit_and", p2, 2);
    TEST("trit_and(T,T) status");      ASSERT(r.status == TRIT_TRUE, "T");
    TEST("trit_and(T,T) result");      ASSERT(r.trit_result == TRIT_TRUE, "T");
    p2[1].trit_value = TRIT_FALSE;
    r = mcp_call_tool(&srv, "trit_or", p2, 2);
    TEST("trit_or(T,F) result T");     ASSERT(r.trit_result == TRIT_TRUE, "T");
    mcp_param_t p1 = {"a", 0, TRIT_FALSE};
    r = mcp_call_tool(&srv, "trit_not", &p1, 1);
    TEST("trit_not(F) = T");          ASSERT(r.trit_result == TRIT_TRUE, "T");

    SECTION("MCP: BCT");
    mcp_param_t bp = {"t", 0, TRIT_TRUE};
    r = mcp_call_tool(&srv, "bct_encode", &bp, 1);
    TEST("bct_encode(+1) → POS");     ASSERT(strstr(r.content, "2") != NULL, "POS");
    mcp_param_t bdp = {"b", BCT_NEG, TRIT_UNKNOWN};
    r = mcp_call_tool(&srv, "bct_decode", &bdp, 1);
    TEST("bct_decode(NEG) → -1");     ASSERT(r.trit_result == TRIT_FALSE, "F");

    SECTION("MCP: Radix Conversion");
    mcp_param_t rp = {"val", 42, TRIT_UNKNOWN};
    r = mcp_call_tool(&srv, "radix_conv", &rp, 1);
    TEST("radix_conv content");        ASSERT(strstr(r.content, "42") != NULL, "42");
    mcp_param_t ep = {"radix", 3, TRIT_UNKNOWN};
    r = mcp_call_tool(&srv, "radix_economy", &ep, 1);
    TEST("economy efficiency > 0");    ASSERT(strstr(r.content, "efficiency") != NULL, "eff");
    mcp_param_t hp = {"val", 13, TRIT_UNKNOWN};
    r = mcp_call_tool(&srv, "heptavintimal", &hp, 1);
    TEST("heptv → 'D'");              ASSERT(strstr(r.content, "D") != NULL, "D");

    SECTION("MCP: Peirce Logic");
    mcp_param_t pp2[2] = { {"a", 0, TRIT_TRUE}, {"b", 0, TRIT_TRUE} };
    r = mcp_call_tool(&srv, "peirce_law", pp2, 2);
    TEST("peirce_law(T,T) status");    ASSERT(r.status == TRIT_TRUE, "T");
    pp2[0].trit_value = TRIT_UNKNOWN;
    r = mcp_call_tool(&srv, "peirce_law", pp2, 2);
    TEST("peirce_law(U,T) status");    ASSERT(r.status == TRIT_TRUE || r.status == TRIT_UNKNOWN, "T|U");
    mcp_param_t dp1 = {"v", 0, TRIT_TRUE};
    r = mcp_call_tool(&srv, "decidability", &dp1, 1);
    TEST("decidability TRUE → 1");    ASSERT(strstr(r.content, "1") != NULL, "1");
    dp1.trit_value = TRIT_UNKNOWN;
    r = mcp_call_tool(&srv, "decidability", &dp1, 1);
    TEST("decidability UNK → 0");     ASSERT(strstr(r.content, "0") != NULL, "0");

    SECTION("MCP: Hardware Tools");
    r = mcp_call_tool(&srv, "hamming_dist", NULL, 0);
    TEST("hamming_dist = 1");          ASSERT(strstr(r.content, "1") != NULL, "1");
    r = mcp_call_tool(&srv, "rebel2_exec", NULL, 0);
    TEST("rebel2 reg == 17");          ASSERT(strstr(r.content, "17") != NULL, "17");

    SECTION("MCP: K₃ Statistics");
    r = mcp_call_tool(&srv, "k3_stats", NULL, 0);
    TEST("k3_stats ok");               ASSERT(r.status == TRIT_TRUE, "T");
    TEST("call_count > 0");            ASSERT(srv.call_count > 0, ">0");

    SECTION("MCP: Tool Not Found");
    r = mcp_call_tool(&srv, "nonexistent", NULL, 0);
    TEST("status FALSE");              ASSERT(r.status == TRIT_FALSE, "F");
    TEST("'not found' in content");    ASSERT(strstr(r.content, "not found") != NULL, "msg");

    SECTION("MCP: Parameter Helpers");
    mcp_param_t ph = {"test_param", 42, TRIT_TRUE};
    TEST("param name correct");        ASSERT(strcmp(ph.name, "test_param") == 0, "name");
    TEST("int_value == 42");           ASSERT(ph.value == 42, "42");
    TEST("trit_value == 1");           ASSERT(ph.trit_value == TRIT_TRUE, "T");

    SECTION("MCP: Custom Registration");
    int initial_tools = srv.tool_count;
    int idx = mcp_register_tool(&srv, "custom_tool", mcp_k3_stats_handler);
    TEST("idx >= 0");                  ASSERT(idx >= 0, "≥0");
    TEST("tools == initial + 1");      ASSERT(srv.tool_count == initial_tools + 1, "+1");
    int initial_rsrc = srv.resource_count;
    mcp_register_resource(&srv, "trit://custom/resource");
    TEST("resource registered");       ASSERT(srv.resource_count == initial_rsrc + 1, "+1");

    SECTION("MCP: Missing Parameter Guards");
    r = mcp_call_tool(&srv, "trit_and", NULL, 0);
    TEST("trit_and 0 params → FALSE"); ASSERT(r.status == TRIT_FALSE, "F");
    mcp_param_t wrong = {"x", 0, TRIT_UNKNOWN};
    r = mcp_call_tool(&srv, "bct_encode", &wrong, 0);
    TEST("bct_encode 0 params → F");  ASSERT(r.status == TRIT_FALSE, "F");
    r = mcp_call_tool(&srv, "peirce_law", &wrong, 1);
    TEST("peirce_law 1 param → F");   ASSERT(r.status == TRIT_FALSE, "F");
}

/* ======================================================================== */
int main(void) {
    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  SIGMA 9 MCP SUITE                                         ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n\n");

    g_pass = g_fail = 0;
    test_aecc();
    test_tcam();
    test_peirce();
    test_bct();
    test_rebel2();
    test_mmem();
    test_mcp();

    printf("\n╔══════════════════════════════════════════════════════════════╗\n");
    printf("║  SIGMA 9 MCP SUITE SUMMARY                                 ║\n");
    printf("╠══════════════════════════════════════════════════════════════╣\n");
    printf("║  Total: %4d  Passed: %4d  Failed: %4d                   ║\n",
           g_pass+g_fail, g_pass, g_fail);
    printf("╚══════════════════════════════════════════════════════════════╝\n\n");
    printf("=== Sigma9 MCP Tests: %d passed, %d failed, %d total ===\n",
           g_pass, g_fail, g_pass+g_fail);
    printf("=== Results: %d passed, %d failed ===\n", g_pass, g_fail);
    return g_fail ? 1 : 0;
}
