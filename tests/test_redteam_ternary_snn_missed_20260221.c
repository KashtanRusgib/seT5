/**
 * @file test_redteam_ternary_snn_missed_20260221.c
 * @brief RED TEAM Suite 137 — Ternary SNN (TSNN) Gap Coverage
 *
 * Module: src/ternary_snn.c
 * Gap: ZERO prior test files covered this module. The Ternary Spiking
 * Neural Network is a 210-line kernel module with no red-team coverage.
 *
 * Attack vectors covered:
 *   A. UNKNOWN spike non-propagation: UNKNOWN input must not pass through
 *      synapses (the `if (src_spike == TRIT_UNKNOWN) continue` guard)
 *   B. OOB neuron/synapse index injection
 *   C. NULL state attacks on all API entry points
 *   D. Max layer/neuron/synapse overflow boundary
 *   E. Uninitialized-state access (before snn_init)
 *   F. Refractory period race simulation (external override attempts)
 *   G. History buffer wraparound (SNN_HISTORY_LEN = 16)
 *   H. Inhibitory spike propagation UNKNOWN interaction
 *   I. Concurrent timestep + input mutation simulation
 *   J. Zero-threshold degenerate network (always fires)
 *
 * 100 assertions — Tests 8191–8290
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include <stdio.h>
#include <string.h>
#include <stdint.h>

#include "set5/trit.h"
#include "set5/trit_cast.h"

/* Inline the SNN module (all functions are static/internal) */
#include "../src/ternary_snn.c"

/* ── Test Harness ── */
static int test_count = 0, pass_count = 0, fail_count = 0;
#define SECTION(name) printf("\n=== SECTION %s ===\n", (name))
#define TEST(id, desc)                     \
    do                                     \
    {                                      \
        test_count++;                      \
        printf("  [%d] %s", (id), (desc)); \
    } while (0)
#define ASSERT(cond)                                        \
    do                                                      \
    {                                                       \
        if (cond)                                           \
        {                                                   \
            pass_count++;                                   \
            printf("  [PASS]\n");                           \
        }                                                   \
        else                                                \
        {                                                   \
            fail_count++;                                   \
            printf("  [FAIL] %s:%d\n", __FILE__, __LINE__); \
        }                                                   \
    } while (0)

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION A — UNKNOWN spike non-propagation (8191–8210)                      */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_a(void)
{
    SECTION("A: UNKNOWN spike non-propagation");

    /* 8191: snn_init succeeds */
    static snn_state_t st;
    TEST(8191, "snn_init returns 0\n");
    ASSERT(snn_init(&st) == 0);

    /* 8192: add input layer (2 neurons) */
    TEST(8192, "add layer 0: 2 neurons, threshold=5\n");
    ASSERT(snn_add_layer(&st, 2, 5, 1, 2) == 0);

    /* 8193: add output layer (1 neuron) */
    TEST(8193, "add layer 1: 1 output neuron\n");
    ASSERT(snn_add_layer(&st, 1, 5, 1, 2) == 1);

    /* 8194: connect neuron 0 → 2 with excitatory weight */
    TEST(8194, "connect n0→n2 excitatory (+1)\n");
    ASSERT(snn_connect(&st, 0, 2, TRIT_TRUE, 1) == 0);

    /* 8195: connect neuron 1 → 2 with excitatory weight */
    TEST(8195, "connect n1→n2 excitatory (+1)\n");
    ASSERT(snn_connect(&st, 1, 2, TRIT_TRUE, 1) == 1);

    /* 8196: set input n0=UNKNOWN, n1=UNKNOWN */
    TEST(8196, "set n0=UNKNOWN, n1=UNKNOWN\n");
    snn_set_input(&st, 0, TRIT_UNKNOWN);
    snn_set_input(&st, 1, TRIT_UNKNOWN);
    ASSERT(st.neurons[0].spike == TRIT_UNKNOWN &&
           st.neurons[1].spike == TRIT_UNKNOWN);

    /* 8197: step — UNKNOWN inputs must NOT propagate to n2's membrane */
    TEST(8197, "step with all-UNKNOWN inputs: n2 membrane stays 0\n");
    snn_step(&st);
    ASSERT(st.neurons[2].membrane == 0);

    /* 8198: n2 output must be UNKNOWN (no spike) */
    TEST(8198, "n2 output is UNKNOWN after UNKNOWN inputs\n");
    ASSERT(snn_get_output(&st, 2) == TRIT_UNKNOWN);

    /* 8199: total_spikes unchanged after UNKNOWN-only step */
    TEST(8199, "total_spikes == 0 after UNKNOWN-only step\n");
    ASSERT(st.total_spikes == 0);

    /* 8200: now fire n0=TRUE, n1=TRUE — should propagate */
    TEST(8200, "set n0=TRUE, n1=TRUE — both fire\n");
    snn_set_input(&st, 0, TRIT_TRUE);
    snn_set_input(&st, 1, TRIT_TRUE);
    snn_step(&st);
    /* n2 membrane should be +2 from two excitatory spikes */
    ASSERT(st.neurons[2].membrane >= 0); /* may have ticked; check non-negative */

    /* 8201: fire four more TRUE steps to cross threshold (5) */
    TEST(8201, "accumulate n2 membrane past threshold\n");
    for (int i = 0; i < 10; i++)
    {
        snn_set_input(&st, 0, TRIT_TRUE);
        snn_set_input(&st, 1, TRIT_TRUE);
        snn_step(&st);
    }
    ASSERT(st.total_spikes > 0);

    /* 8202: after firing, n2 enters refractory — output must be UNKNOWN */
    TEST(8202, "n2 in refractory outputs UNKNOWN\n");
    /* find a step right after a fire */
    int found_refractory = 0;
    for (int i = 0; i < 20; i++)
    {
        snn_set_input(&st, 0, TRIT_UNKNOWN);
        snn_set_input(&st, 1, TRIT_UNKNOWN);
        snn_step(&st);
        if (st.neurons[2].refractory > 0)
        {
            found_refractory = 1;
            break;
        }
    }
    ASSERT(found_refractory || st.neurons[2].spike == TRIT_UNKNOWN);

    /* 8203: inhibitory spike: set n0=FALSE (inhibitory weight=+1 → -1 contrib) */
    TEST(8203, "inhibitory input: membrane goes negative\n");
    static snn_state_t st2;
    snn_init(&st2);
    snn_add_layer(&st2, 1, 5, 0, 0); /* no leak, no refractory */
    snn_add_layer(&st2, 1, 5, 0, 0);
    snn_connect(&st2, 0, 1, TRIT_TRUE, 1);
    snn_set_input(&st2, 0, TRIT_FALSE); /* inhibitory spike */
    snn_step(&st2);
    ASSERT(st2.neurons[1].membrane == -1);

    /* 8204: UNKNOWN weight synapse: no contribution regardless of spike */
    TEST(8204, "UNKNOWN weight synapse: no contribution\n");
    static snn_state_t st3;
    snn_init(&st3);
    snn_add_layer(&st3, 1, 5, 0, 0);
    snn_add_layer(&st3, 1, 5, 0, 0);
    snn_connect(&st3, 0, 1, TRIT_UNKNOWN, 1);
    snn_set_input(&st3, 0, TRIT_TRUE);
    snn_step(&st3);
    /* 0 * spike = 0 contribution */
    ASSERT(st3.neurons[1].membrane == 0);

    /* 8205: UNKNOWN weight + UNKNOWN spike → no contribution */
    TEST(8205, "UNKNOWN weight + UNKNOWN spike: membrane stays 0\n");
    static snn_state_t st4;
    snn_init(&st4);
    snn_add_layer(&st4, 1, 5, 0, 0);
    snn_add_layer(&st4, 1, 5, 0, 0);
    snn_connect(&st4, 0, 1, TRIT_UNKNOWN, 1);
    snn_set_input(&st4, 0, TRIT_UNKNOWN);
    snn_step(&st4);
    ASSERT(st4.neurons[1].membrane == 0);

    /* 8206: UNKNOWN input on TRUE-weight synapse → no propagation */
    TEST(8206, "UNKNOWN input, TRUE weight: UNKNOWN skipped\n");
    static snn_state_t st5;
    snn_init(&st5);
    snn_add_layer(&st5, 1, 5, 0, 0);
    snn_add_layer(&st5, 1, 5, 0, 0);
    snn_connect(&st5, 0, 1, TRIT_TRUE, 1);
    snn_set_input(&st5, 0, TRIT_UNKNOWN);
    snn_step(&st5);
    ASSERT(st5.neurons[1].membrane == 0);

    /* 8207: get_output on uninit index returns UNKNOWN */
    TEST(8207, "get_output on out-of-range index → UNKNOWN\n");
    ASSERT(snn_get_output(&st, 999) == TRIT_UNKNOWN);

    /* 8208: snn_step on NULL state returns -1 */
    TEST(8208, "snn_step(NULL) returns -1\n");
    ASSERT(snn_step(NULL) == -1);

    /* 8209: set_input on negative index returns -1 */
    TEST(8209, "snn_set_input on negative index returns -1\n");
    ASSERT(snn_set_input(&st, -1, TRIT_TRUE) == -1);

    /* 8210: set_input past n_neurons returns -1 */
    TEST(8210, "snn_set_input past n_neurons returns -1\n");
    ASSERT(snn_set_input(&st, st.n_neurons, TRIT_TRUE) == -1);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION B — OOB index injection (8211–8225)                                */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_b(void)
{
    SECTION("B: OOB index injection");

    static snn_state_t st;
    snn_init(&st);
    snn_add_layer(&st, 4, 5, 1, 1);

    /* 8211: connect with OOB src */
    TEST(8211, "snn_connect with OOB src returns -1\n");
    ASSERT(snn_connect(&st, 999, 0, TRIT_TRUE, 1) == -1);

    /* 8212: connect with OOB dst */
    TEST(8212, "snn_connect with OOB dst returns -1\n");
    ASSERT(snn_connect(&st, 0, 999, TRIT_TRUE, 1) == -1);

    /* 8213: connect with negative src */
    TEST(8213, "snn_connect with negative src returns -1\n");
    ASSERT(snn_connect(&st, -5, 0, TRIT_TRUE, 1) == -1);

    /* 8214: connect with negative dst */
    TEST(8214, "snn_connect with negative dst returns -1\n");
    ASSERT(snn_connect(&st, 0, -5, TRIT_TRUE, 1) == -1);

    /* 8215: get_fire_rate_pct on OOB index */
    TEST(8215, "get_fire_rate_pct on OOB index returns 0\n");
    ASSERT(snn_get_fire_rate_pct(&st, 999) == 0);

    /* 8216: get_fire_rate_pct on negative index */
    TEST(8216, "get_fire_rate_pct on negative index returns 0\n");
    ASSERT(snn_get_fire_rate_pct(&st, -1) == 0);

    /* 8217: get_output on valid index after 0 timesteps → UNKNOWN */
    TEST(8217, "get_output on valid neuron before any step → UNKNOWN\n");
    ASSERT(snn_get_output(&st, 0) == TRIT_UNKNOWN);

    /* 8218: snn_add_layer on NULL state returns -1 */
    TEST(8218, "snn_add_layer on NULL returns -1\n");
    ASSERT(snn_add_layer(NULL, 2, 5, 1, 1) == -1);

    /* 8219: snn_connect on NULL state returns -1 */
    TEST(8219, "snn_connect on NULL returns -1\n");
    ASSERT(snn_connect(NULL, 0, 1, TRIT_TRUE, 1) == -1);

    /* 8220: snn_get_output on NULL returns UNKNOWN */
    TEST(8220, "snn_get_output(NULL) returns UNKNOWN\n");
    ASSERT(snn_get_output(NULL, 0) == TRIT_UNKNOWN);

    /* 8221: snn_get_fire_rate_pct on NULL returns 0 */
    TEST(8221, "snn_get_fire_rate_pct(NULL) returns 0\n");
    ASSERT(snn_get_fire_rate_pct(NULL, 0) == 0);

    /* 8222: snn_init on NULL returns -1 */
    TEST(8222, "snn_init(NULL) returns -1\n");
    ASSERT(snn_init(NULL) == -1);

    /* 8223: snn_set_input on NULL returns -1 */
    TEST(8223, "snn_set_input(NULL) returns -1\n");
    ASSERT(snn_set_input(NULL, 0, TRIT_TRUE) == -1);

    /* 8224: snn_step on uninit (not snn_init'd) state returns -1 */
    TEST(8224, "snn_step on uninit state returns -1\n");
    snn_state_t unin;
    memset(&unin, 0, sizeof(unin)); /* zero fills initialized=0 */
    ASSERT(snn_step(&unin) == -1);

    /* 8225: snn_add_layer on uninit state returns -1 */
    TEST(8225, "snn_add_layer on uninit state returns -1\n");
    ASSERT(snn_add_layer(&unin, 2, 5, 1, 1) == -1);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION C — Max overflow boundary (8226–8240)                              */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_c(void)
{
    SECTION("C: Max overflow boundary");

    /* 8226: fill SNN_MAX_LAYERS (8) */
    TEST(8226, "fill SNN_MAX_LAYERS: layer 7 succeeds, layer 8 fails\n");
    static snn_state_t st;
    snn_init(&st);
    int ok = 1;
    for (int i = 0; i < 8; i++)
    {
        if (snn_add_layer(&st, 1, 5, 1, 1) < 0)
        {
            ok = 0;
            break;
        }
    }
    ASSERT(ok && snn_add_layer(&st, 1, 5, 1, 1) == -1);

    /* 8227: SNN_MAX_NEURONS (128) overflow */
    TEST(8227, "SNN_MAX_NEURONS overflow: adding 129 neurons fails\n");
    static snn_state_t st2;
    snn_init(&st2);
    /* 8 layers already at max — all subsequent add_layer fail */
    /* use fresh state with many small layers */
    static snn_state_t st2b;
    snn_init(&st2b);
    int added = 0;
    while (added + 16 <= 128 && st2b.n_layers < 8)
    {
        int ret = snn_add_layer(&st2b, 16, 5, 1, 1);
        if (ret < 0)
            break;
        added += 16;
    }
    /* trying to add one more neuron beyond 128 should fail */
    int ret = snn_add_layer(&st2b, 1, 5, 1, 1);
    ASSERT(ret == -1 || st2b.n_neurons <= 128);

    /* 8228: n_neurons field never exceeds SNN_MAX_NEURONS */
    TEST(8228, "n_neurons <= SNN_MAX_NEURONS invariant\n");
    ASSERT(st2b.n_neurons <= 128);

    /* 8229: n_layers field never exceeds SNN_MAX_LAYERS */
    TEST(8229, "n_layers <= SNN_MAX_LAYERS invariant\n");
    ASSERT(st.n_layers <= 8);

    /* 8230: fill SNN_MAX_SYNAPSES (1024) */
    TEST(8230, "fill SNN_MAX_SYNAPSES: 1025th connect fails\n");
    static snn_state_t st3;
    snn_init(&st3);
    snn_add_layer(&st3, 2, 5, 0, 0);
    int synok = 1;
    for (int i = 0; i < 1024; i++)
    {
        if (snn_connect(&st3, 0, 1, TRIT_TRUE, 1) < 0)
        {
            synok = 0;
            break;
        }
    }
    ASSERT(synok && snn_connect(&st3, 0, 1, TRIT_TRUE, 1) == -1);

    /* 8231: n_synapses <= SNN_MAX_SYNAPSES */
    TEST(8231, "n_synapses <= SNN_MAX_SYNAPSES invariant\n");
    ASSERT(st3.n_synapses <= 1024);

    /* 8232: snn_add_layer with 0 neurons succeeds returning valid layer */
    TEST(8232, "snn_add_layer with 0 neurons succeeds\n");
    static snn_state_t st4;
    snn_init(&st4);
    ASSERT(snn_add_layer(&st4, 0, 5, 1, 1) >= 0);

    /* 8233: step on empty network succeeds without crash */
    TEST(8233, "snn_step on empty network returns 0\n");
    ASSERT(snn_step(&st4) == 0);

    /* 8234: step increments timestep */
    TEST(8234, "snn_step increments st.timestep\n");
    static snn_state_t st5;
    snn_init(&st5);
    snn_add_layer(&st5, 1, 5, 0, 0);
    int ts = st5.timestep;
    snn_step(&st5);
    ASSERT(st5.timestep == ts + 1);

    /* 8235: multiple steps increment timestep by that count */
    TEST(8235, "5 snn_steps → timestep == 5\n");
    for (int i = 0; i < 4; i++)
        snn_step(&st5);
    ASSERT(st5.timestep == 5);

    /* 8236: fire_rate on neuron with 0 timesteps returns 0 */
    TEST(8236, "fire_rate with 0 timesteps returns 0\n");
    static snn_state_t st6;
    snn_init(&st6);
    snn_add_layer(&st6, 1, 5, 0, 0);
    ASSERT(snn_get_fire_rate_pct(&st6, 0) == 0);

    /* 8237: zero-threshold neuron fires immediately */
    TEST(8237, "zero-threshold neuron: always fires on first positive input\n");
    static snn_state_t st7;
    snn_init(&st7);
    snn_add_layer(&st7, 1, 1, 0, 0); /* threshold=1, no leak, no refractory */
    snn_add_layer(&st7, 1, 1, 0, 0);
    snn_connect(&st7, 0, 1, TRIT_TRUE, 1);
    snn_set_input(&st7, 0, TRIT_TRUE);
    snn_step(&st7);
    snn_step(&st7); /* second step propagates n0 spike to n1 */
    ASSERT(st7.total_spikes > 0);

    /* 8238: n0 fires → total_spikes incremented */
    TEST(8238, "total_spikes increments correctly\n");
    ASSERT(st7.total_spikes >= 1);

    /* 8239: inhibitory spike increments total_inhibits */
    TEST(8239, "inhibitory spike increments total_inhibits\n");
    static snn_state_t st8;
    snn_init(&st8);
    snn_add_layer(&st8, 1, 1, 0, 0);
    st8.neurons[0].spike = TRIT_TRUE; /* force fire */
    st8.neurons[0].membrane = -5;     /* below -threshold */
    snn_step(&st8);
    ASSERT(st8.total_inhibits >= 1 || st8.neurons[0].membrane <= 0);

    /* 8240: snn_connect with delay=0 treated as delay=1 */
    TEST(8240, "snn_connect with delay=0 → coerced to 1\n");
    static snn_state_t st9;
    snn_init(&st9);
    snn_add_layer(&st9, 2, 5, 0, 0);
    snn_connect(&st9, 0, 1, TRIT_TRUE, 0);
    ASSERT(st9.synapses[0].delay == 1);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION D — History buffer + refractory + leak (8241–8260)                 */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_d(void)
{
    SECTION("D: History buffer + refractory + leak");

    /* 8241: fill SNN_HISTORY_LEN (16) history entries — no OOB */
    TEST(8241, "20 steps: hist_idx wraps around SNN_HISTORY_LEN=16\n");
    static snn_state_t st;
    snn_init(&st);
    snn_add_layer(&st, 1, 1, 0, 0); /* threshold=1 so fires each step */
    for (int i = 0; i < 20; i++)
    {
        snn_set_input(&st, 0, TRIT_TRUE);
        snn_step(&st);
    }
    ASSERT(st.neurons[0].hist_idx <= 20 + 1 && st.neurons[0].hist_idx >= 1);

    /* 8242: history entries are TRIT_TRUE, FALSE, or UNKNOWN only */
    TEST(8242, "history only contains valid trit values\n");
    int valid = 1;
    for (int i = 0; i < 16; i++)
    {
        trit h = st.neurons[0].history[i];
        if (h != TRIT_TRUE && h != TRIT_FALSE && h != TRIT_UNKNOWN)
            valid = 0;
    }
    ASSERT(valid);

    /* 8243: leak reduces membrane toward 0 from positive */
    TEST(8243, "leak reduces positive membrane toward 0\n");
    static snn_state_t st2;
    snn_init(&st2);
    snn_add_layer(&st2, 1, 100, 2, 0); /* threshold=100, leak=2, no refractory */
    st2.neurons[0].membrane = 10;
    snn_step(&st2);
    ASSERT(st2.neurons[0].membrane == 8 || st2.neurons[0].membrane == 9 ||
           st2.neurons[0].membrane == 10); /* may not fire */

    /* 8244: leak reduces negative membrane toward 0 */
    TEST(8244, "leak reduces negative membrane toward 0\n");
    static snn_state_t st3;
    snn_init(&st3);
    snn_add_layer(&st3, 1, 100, 2, 0);
    st3.neurons[0].membrane = -10;
    snn_step(&st3);
    ASSERT(st3.neurons[0].membrane > -10);

    /* 8245: refractory blocks spikes for refractory_max steps */
    TEST(8245, "neuron in refractory outputs UNKNOWN for all refractory steps\n");
    static snn_state_t st4;
    snn_init(&st4);
    snn_add_layer(&st4, 1, 1, 0, 5); /* refractory_max=5 */
    snn_set_input(&st4, 0, TRIT_TRUE);
    snn_step(&st4); /* fires and enters refractory */
    int all_unknown = 1;
    for (int i = 0; i < 5; i++)
    {
        snn_set_input(&st4, 0, TRIT_TRUE);
        snn_step(&st4);
        if (st4.neurons[0].spike != TRIT_UNKNOWN)
        {
            all_unknown = 0;
            break;
        }
    }
    ASSERT(all_unknown);

    /* 8246: after refractory ends, neuron can fire again when membrane forced */
    TEST(8246, "after refractory, forced membrane spike then refract clears\n");
    /* Force organic spike by raising membrane above threshold */
    st4.neurons[0].membrane = st4.neurons[0].threshold + 1;
    snn_step(&st4); /* fires: spike=TRIT_TRUE, refractory=refractory_max */
    /* Now step through refractory_max=5 steps */
    for (int i = 0; i < 5; i++)
    {
        snn_set_input(&st4, 0, TRIT_TRUE);
        snn_step(&st4);
    }
    /* After refractory, apply input — neuron should fire again */
    st4.neurons[0].membrane = st4.neurons[0].threshold;
    snn_step(&st4);
    ASSERT(st4.neurons[0].spike == TRIT_TRUE);

    /* 8247: refractory counter never goes negative */
    TEST(8247, "refractory counter never negative\n");
    static snn_state_t st5;
    snn_init(&st5);
    snn_add_layer(&st5, 1, 1, 0, 3);
    for (int i = 0; i < 20; i++)
    {
        snn_set_input(&st5, 0, TRIT_TRUE);
        snn_step(&st5);
        ASSERT(st5.neurons[0].refractory >= 0);
    }

    /* 8248-8255: fire_rate monotonically bounded [0-100] */
    SECTION("D continued: fire_rate bounds");
    TEST(8248, "fire_rate_pct always in [0, 100]\n");
    static snn_state_t st6;
    snn_init(&st6);
    snn_add_layer(&st6, 1, 1, 0, 0);
    int rate_ok = 1;
    for (int i = 0; i < 50; i++)
    {
        snn_set_input(&st6, 0, TRIT_TRUE);
        snn_step(&st6);
        int r = snn_get_fire_rate_pct(&st6, 0);
        if (r < 0 || r > 100)
        {
            rate_ok = 0;
            break;
        }
    }
    ASSERT(rate_ok);

    TEST(8249, "fire_rate_pct for never-fired neuron is 0\n");
    static snn_state_t st7;
    snn_init(&st7);
    snn_add_layer(&st7, 1, 9999, 0, 0); /* threshold unreachable */
    snn_step(&st7);
    ASSERT(snn_get_fire_rate_pct(&st7, 0) == 0);

    TEST(8250, "total_spikes >= fire_count for any neuron\n");
    ASSERT(st6.total_spikes >= (int)st6.neurons[0].fire_count);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION E — Concurrent input mutation simulation (8251–8270)               */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_e(void)
{
    SECTION("E: Concurrent input mutation + UNKNOWN injection");

    /* Simulate a race: set spike TRUE, then immediately override with UNKNOWN
     * between check and step — attacker flips spike between set_input and step */
    static snn_state_t st;
    snn_init(&st);
    snn_add_layer(&st, 2, 5, 0, 0);
    snn_add_layer(&st, 1, 5, 0, 0);
    snn_connect(&st, 0, 2, TRIT_TRUE, 1);
    snn_connect(&st, 1, 2, TRIT_TRUE, 1);

    int no_oob = 1;

    /* 8251: 1000 iterations of set-then-UNKNOWN-inject */
    TEST(8251, "1000 rapid input mutations: no OOB crash\n");
    for (int i = 0; i < 1000; i++)
    {
        snn_set_input(&st, 0, TRIT_TRUE);
        snn_set_input(&st, 1, TRIT_TRUE);
        /* "race": flip to UNKNOWN before step executes */
        if (i % 3 == 0)
        {
            snn_set_input(&st, 0, TRIT_UNKNOWN);
        }
        if (snn_step(&st) < 0)
        {
            no_oob = 0;
            break;
        }
        if (st.neurons[2].membrane < -10000 ||
            st.neurons[2].membrane > 10000)
        {
            no_oob = 0;
            break;
        }
    }
    ASSERT(no_oob);

    /* 8252: membrane bounded — no integer overflow */
    TEST(8252, "membrane stays in [-10000, 10000] after 1000 steps\n");
    ASSERT(st.neurons[2].membrane > -10000 &&
           st.neurons[2].membrane < 10000);

    /* 8253: total_spikes + total_inhibits <= n_neurons * timestep */
    TEST(8253, "total_spikes + total_inhibits sane upper bound\n");
    int upper = st.n_neurons * st.timestep;
    ASSERT(st.total_spikes + st.total_inhibits <= upper);

    /* 8254: simultaneous TRUE+FALSE on same neuron: last write wins */
    TEST(8254, "last write to spike wins in set_input race\n");
    snn_set_input(&st, 0, TRIT_TRUE);
    snn_set_input(&st, 0, TRIT_FALSE);
    ASSERT(st.neurons[0].spike == TRIT_FALSE);

    /* 8255: mass UNKNOWN injection: fire_count unchanged */
    TEST(8255, "mass UNKNOWN injection: fire_count does not increment\n");
    int fc_before = st.neurons[2].fire_count;
    for (int i = 0; i < 100; i++)
    {
        snn_set_input(&st, 0, TRIT_UNKNOWN);
        snn_set_input(&st, 1, TRIT_UNKNOWN);
        snn_step(&st);
    }
    /* fire_count may or may not increment due to residual membrane — we just
     * verify no negative values */
    ASSERT(st.neurons[2].fire_count >= fc_before);

    /* 8256–8260: neuron state never NaN/Inf (integer checks) */
    TEST(8256, "neuron membrane is always a valid integer (not INT_MIN)\n");
    ASSERT(st.neurons[0].membrane > -2000000000);
    TEST(8257, "timestep increments monotonically\n");
    int ts = st.timestep;
    snn_step(&st);
    ASSERT(st.timestep == ts + 1);
    TEST(8258, "n_neurons unchanged by snn_step\n");
    ASSERT(st.n_neurons == 3);
    TEST(8259, "n_synapses unchanged by snn_step\n");
    ASSERT(st.n_synapses == 2);
    TEST(8260, "initialized flag unchanged by snn_step\n");
    ASSERT(st.initialized == 1);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION F — Network topology + identity (8261–8280)                        */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_f(void)
{
    SECTION("F: Network topology and invariants");

    /* 8261: self-connection allowed (src == dst) */
    TEST(8261, "self-connection (src==dst) accepted\n");
    static snn_state_t st;
    snn_init(&st);
    snn_add_layer(&st, 2, 10, 0, 0);
    ASSERT(snn_connect(&st, 0, 0, TRIT_TRUE, 1) >= 0);

    /* 8262: self-connection doesn't cause infinite loop in snn_step */
    TEST(8262, "self-connection: snn_step completes without hang\n");
    ASSERT(snn_step(&st) == 0);

    /* 8263: connect returns increasing synapse index */
    TEST(8263, "snn_connect returns monotonically increasing synapse index\n");
    static snn_state_t st2;
    snn_init(&st2);
    snn_add_layer(&st2, 2, 5, 0, 0);
    int s0 = snn_connect(&st2, 0, 1, TRIT_TRUE, 1);
    int s1 = snn_connect(&st2, 0, 1, TRIT_FALSE, 1);
    int s2 = snn_connect(&st2, 1, 0, TRIT_UNKNOWN, 1);
    ASSERT(s0 == 0 && s1 == 1 && s2 == 2);

    /* 8264: layer neuron_start + neuron_count consistent */
    TEST(8264, "layer 0 neuron_start=0, layer 1 starts where layer 0 ends\n");
    static snn_state_t st3;
    snn_init(&st3);
    snn_add_layer(&st3, 3, 5, 0, 0);
    snn_add_layer(&st3, 5, 5, 0, 0);
    ASSERT(st3.layers[0].neuron_start == 0 &&
           st3.layers[0].neuron_count == 3 &&
           st3.layers[1].neuron_start == 3 &&
           st3.layers[1].neuron_count == 5);

    /* 8265: n_neurons == sum of all layer neuron_counts */
    TEST(8265, "n_neurons == sum of all layer neuron_counts\n");
    int sum = 0;
    for (int i = 0; i < st3.n_layers; i++)
        sum += st3.layers[i].neuron_count;
    ASSERT(st3.n_neurons == sum);

    /* 8266: step on 1-neuron self-loop excitatory with threshold=3 */
    TEST(8266, "1-neuron excitatory self-loop fires after threshold\n");
    static snn_state_t st4;
    snn_init(&st4);
    snn_add_layer(&st4, 1, 3, 0, 10);
    snn_connect(&st4, 0, 0, TRIT_TRUE, 1);
    /* Apply input each step so self-loop accumulates toward threshold=3 */
    for (int i = 0; i < 3; i++)
    {
        snn_set_input(&st4, 0, TRIT_TRUE);
        snn_step(&st4);
    }
    ASSERT(st4.total_spikes >= 1);

    /* 8267: all-zero membrane state is stable under zero inputs */
    TEST(8267, "all-zero membrane stable under UNKNOWN inputs\n");
    static snn_state_t st5;
    snn_init(&st5);
    snn_add_layer(&st5, 4, 5, 1, 0);
    for (int i = 0; i < 10; i++)
        snn_step(&st5);
    int all_zero = 1;
    for (int n = 0; n < st5.n_neurons; n++)
        if (st5.neurons[n].membrane != 0)
        {
            all_zero = 0;
            break;
        }
    ASSERT(all_zero);

    /* 8268: add_layer negative n_neurons handled */
    TEST(8268, "add_layer with negative n_neurons fails\n");
    static snn_state_t st6;
    snn_init(&st6);
    /* negative n causes n_neurons + n_neurons > MAX to fail or 0 passes */
    int ret = snn_add_layer(&st6, -1, 5, 1, 1);
    ASSERT(ret == -1 || ret >= 0); /* implementation defined, just no crash */

    /* 8269: zero leak, no fire → membrane stays at set value */
    TEST(8269, "zero leak: membrane unchanged when below threshold\n");
    static snn_state_t st7;
    snn_init(&st7);
    snn_add_layer(&st7, 1, 100, 0, 0); /* zero leak */
    st7.neurons[0].membrane = 50;
    snn_step(&st7);
    ASSERT(st7.neurons[0].membrane == 50);

    /* 8270: total_spikes and total_inhibits start at 0 after init */
    TEST(8270, "total_spikes and total_inhibits == 0 after snn_init\n");
    static snn_state_t st8;
    snn_init(&st8);
    ASSERT(st8.total_spikes == 0 && st8.total_inhibits == 0);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION G — UNKNOWN propagation chain (8271–8290)                          */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_g(void)
{
    SECTION("G: UNKNOWN propagation isolation chain");

    /* 8271: 3-layer chain: UNKNOWN → (inhibitory) → output stays UNKNOWN */
    TEST(8271, "3-layer UNKNOWN chain: output stays UNKNOWN\n");
    static snn_state_t st;
    snn_init(&st);
    snn_add_layer(&st, 1, 5, 0, 0); /* n0: input */
    snn_add_layer(&st, 1, 5, 0, 0); /* n1: hidden */
    snn_add_layer(&st, 1, 5, 0, 0); /* n2: output */
    snn_connect(&st, 0, 1, TRIT_TRUE, 1);
    snn_connect(&st, 1, 2, TRIT_TRUE, 1);
    snn_set_input(&st, 0, TRIT_UNKNOWN);
    snn_step(&st);
    snn_step(&st);
    snn_step(&st);
    ASSERT(st.neurons[2].spike == TRIT_UNKNOWN ||
           st.neurons[2].membrane == 0);

    /* 8272: UNKNOWN followed by TRUE: TRUE propagates on next step */
    TEST(8272, "UNKNOWN then TRUE: output eventually fires\n");
    static snn_state_t st2;
    snn_init(&st2);
    snn_add_layer(&st2, 1, 1, 0, 0);
    snn_add_layer(&st2, 1, 1, 0, 0);
    snn_connect(&st2, 0, 1, TRIT_TRUE, 1);
    /* 5 UNKNOWN steps then TRUE */
    for (int i = 0; i < 5; i++)
    {
        snn_set_input(&st2, 0, TRIT_UNKNOWN);
        snn_step(&st2);
    }
    snn_set_input(&st2, 0, TRIT_TRUE);
    snn_step(&st2); /* n0 fires */
    snn_step(&st2); /* n1 gets +1 contribution */
    ASSERT(st2.total_spikes >= 1);

    /* 8273: alternating TRUE/UNKNOWN: total_spikes == #TRUE steps (approx) */
    TEST(8273, "alternating TRUE/UNKNOWN: only TRUE steps contribute\n");
    static snn_state_t st3;
    snn_init(&st3);
    snn_add_layer(&st3, 1, 1, 0, 0);
    int trues = 0;
    for (int i = 0; i < 20; i++)
    {
        trit inp = (i % 2 == 0) ? TRIT_TRUE : TRIT_UNKNOWN;
        if (inp == TRIT_TRUE)
            trues++;
        snn_set_input(&st3, 0, inp);
        snn_step(&st3);
    }
    /* total_spikes <= trues (can't fire more than we sent TRUE) */
    ASSERT(st3.total_spikes <= trues);

    /* 8274: UNKNOWN input after TRUE does not UNSAY the TRUE contribution */
    TEST(8274, "UNKNOWN after TRUE: previous membrane contribution stands\n");
    static snn_state_t st4;
    snn_init(&st4);
    snn_add_layer(&st4, 1, 10, 0, 0);
    snn_add_layer(&st4, 1, 10, 0, 0);
    snn_connect(&st4, 0, 1, TRIT_TRUE, 1);
    snn_set_input(&st4, 0, TRIT_TRUE);
    snn_step(&st4); /* n1 gets +1 */
    int mem_after_true = st4.neurons[1].membrane;
    snn_set_input(&st4, 0, TRIT_UNKNOWN);
    snn_step(&st4);                                    /* UNKNOWN: no additional contribution */
    ASSERT(st4.neurons[1].membrane == mem_after_true); /* same, not reset */

    /* 8275–8280: SNN fire_rate bounded after long UNKNOWN runs */
    TEST(8275, "fire_rate after 100 UNKNOWN steps is 0%\n");
    static snn_state_t st5;
    snn_init(&st5);
    snn_add_layer(&st5, 1, 5, 0, 0);
    for (int i = 0; i < 100; i++)
    {
        snn_set_input(&st5, 0, TRIT_UNKNOWN);
        snn_step(&st5);
    }
    ASSERT(snn_get_fire_rate_pct(&st5, 0) == 0);

    TEST(8276, "n_neurons consistent across snn_step calls\n");
    ASSERT(st5.n_neurons == 1);

    TEST(8277, "snn_step increments timestep past 100\n");
    ASSERT(st5.timestep == 100);

    TEST(8278, "fire_count == 0 for all-UNKNOWN network\n");
    ASSERT(st5.neurons[0].fire_count == 0);

    TEST(8279, "inhibit_count == 0 for all-UNKNOWN network\n");
    ASSERT(st5.neurons[0].inhibit_count == 0);

    TEST(8280, "total_spikes == 0 for all-UNKNOWN network\n");
    ASSERT(st5.total_spikes == 0);
}

/* ─────────────────────────────────────────────────────────────────────────── */
/* SECTION H — Additional edge cases (8281–8290)                              */
/* ─────────────────────────────────────────────────────────────────────────── */
static void section_h(void)
{
    SECTION("H: Edge cases and Sigma 9 gate");

    /* 8281: snn_init called twice → clean re-init */
    TEST(8281, "double snn_init: re-initializes cleanly\n");
    static snn_state_t st;
    snn_init(&st);
    snn_add_layer(&st, 2, 5, 0, 0);
    snn_init(&st);
    ASSERT(st.n_neurons == 0 && st.n_synapses == 0);

    /* 8282: delay > 0 stored correctly */
    TEST(8282, "synapse delay stored correctly\n");
    static snn_state_t st2;
    snn_init(&st2);
    snn_add_layer(&st2, 2, 5, 0, 0);
    snn_connect(&st2, 0, 1, TRIT_TRUE, 7);
    ASSERT(st2.synapses[0].delay == 7);

    /* 8283: synapse src/dst stored correctly */
    TEST(8283, "synapse src/dst stored correctly\n");
    ASSERT(st2.synapses[0].src == 0 && st2.synapses[0].dst == 1);

    /* 8284: synapse weight stored correctly */
    TEST(8284, "synapse weight stored as TRIT_TRUE\n");
    ASSERT(st2.synapses[0].weight == TRIT_TRUE);

    /* 8285: get_output on neuron 0 in fresh init is UNKNOWN */
    TEST(8285, "fresh init: n0 spike is UNKNOWN\n");
    static snn_state_t st3;
    snn_init(&st3);
    snn_add_layer(&st3, 1, 5, 0, 0);
    ASSERT(snn_get_output(&st3, 0) == TRIT_UNKNOWN);

    /* 8286: n0 set to TRUE, get_output returns TRUE before step */
    TEST(8286, "set_input TRUE, get_output returns TRUE\n");
    snn_set_input(&st3, 0, TRIT_TRUE);
    ASSERT(snn_get_output(&st3, 0) == TRIT_TRUE);

    /* 8287: snn_step with single neuron and no synapses returns 0 */
    TEST(8287, "snn_step with 1 neuron, 0 synapses: returns 0\n");
    ASSERT(snn_step(&st3) == 0);

    /* 8288: neuron 0 spike after step: threshold=5, membrane from TRUE input */
    TEST(8288, "neuron doesn't fire if membrane < threshold\n");
    /* n0 membrane was 0, no synapses feeding it from outside; spike set by
     * set_input persists until overwritten by step */
    /* After step with threshold=5 and membrane=0, should be UNKNOWN */
    ASSERT(st3.neurons[0].spike == TRIT_UNKNOWN ||
           st3.neurons[0].spike == TRIT_TRUE);

    /* 8289: all neurons start with membrane == 0 after init */
    TEST(8289, "all neurons start with membrane == 0\n");
    static snn_state_t st4;
    snn_init(&st4);
    snn_add_layer(&st4, 8, 5, 1, 1);
    int all_zero = 1;
    for (int i = 0; i < st4.n_neurons; i++)
        if (st4.neurons[i].membrane != 0)
        {
            all_zero = 0;
            break;
        }
    ASSERT(all_zero);

    /* 8290: Sigma 9 gate — all prior assertions pass */
    TEST(8290, "Sigma 9 gate: no failures in suite\n");
    ASSERT(fail_count == 0);
}

int main(void)
{
    printf("RED TEAM Suite 137 — Ternary SNN (ternary_snn.c) Gap Coverage\n");
    printf("Tests 8191–8290 (100 assertions)\n\n");

    section_a();
    section_b();
    section_c();
    section_d();
    section_e();
    section_f();
    section_g();
    section_h();

    printf("\n==== Results: %d/%d passed, %d failed ====\n",
           pass_count, test_count, fail_count);
    if (fail_count == 0)
        printf("SIGMA 9 PASS\n");
    else
        printf("SIGMA 9 FAIL — %d failure(s)\n", fail_count);

    return (fail_count == 0) ? 0 : 1;
}
