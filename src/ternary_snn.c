/**
 * @file ternary_snn.c
 * @brief T-042: Ternary Spiking Neural Network (TSNN)
 *
 * Inspired by CTSN (Ternary SNN) research: natural mapping of
 * spike(+1), no-spike(0), inhibit(-1) to balanced ternary.
 *
 * Architecture:
 *   - Leaky Integrate-and-Fire (LIF) neurons with ternary membrane
 *   - Ternary synaptic weights: excitatory(+1), silent(0), inhibitory(-1)
 *   - Spike propagation uses trit multiplication
 *   - Temporal coding via ternary time steps
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/trit.h"
#include <stdint.h>
#include <string.h>

/* ── Configuration ── */
#define SNN_MAX_NEURONS    128
#define SNN_MAX_SYNAPSES   1024
#define SNN_MAX_LAYERS     8
#define SNN_HISTORY_LEN    16

/* ── Neuron state ── */
typedef struct {
    int     membrane;           /* membrane potential (integer) */
    int     threshold;          /* firing threshold */
    int     leak;               /* leak rate per timestep */
    trit    spike;              /* current output: +1=fire, 0=rest, -1=inhibit */
    trit    history[SNN_HISTORY_LEN]; /* spike history */
    int     hist_idx;
    int     fire_count;
    int     inhibit_count;
    int     refractory;         /* refractory period counter */
    int     refractory_max;     /* refractory period */
} snn_neuron_t;

/* ── Synapse ── */
typedef struct {
    int     src;                /* source neuron index */
    int     dst;                /* destination neuron index */
    trit    weight;             /* +1=excitatory, 0=silent, -1=inhibitory */
    int     delay;              /* propagation delay (timesteps) */
} snn_synapse_t;

/* ── Layer ── */
typedef struct {
    int     neuron_start;       /* first neuron index in this layer */
    int     neuron_count;       /* neurons in this layer */
} snn_layer_t;

/* ── Network state ── */
typedef struct {
    snn_neuron_t  neurons[SNN_MAX_NEURONS];
    snn_synapse_t synapses[SNN_MAX_SYNAPSES];
    snn_layer_t   layers[SNN_MAX_LAYERS];
    int           n_neurons;
    int           n_synapses;
    int           n_layers;
    int           timestep;
    int           total_spikes;
    int           total_inhibits;
    int           initialized;
} snn_state_t;

/* ── API ── */

int snn_init(snn_state_t *st) {
    if (!st) return -1;
    memset(st, 0, sizeof(*st));
    st->initialized = 1;
    return 0;
}

int snn_add_layer(snn_state_t *st, int n_neurons, int threshold,
                   int leak, int refractory) {
    if (!st || !st->initialized) return -1;
    if (st->n_layers >= SNN_MAX_LAYERS) return -1;
    if (st->n_neurons + n_neurons > SNN_MAX_NEURONS) return -1;

    snn_layer_t *layer = &st->layers[st->n_layers];
    layer->neuron_start = st->n_neurons;
    layer->neuron_count = n_neurons;

    for (int i = 0; i < n_neurons; i++) {
        snn_neuron_t *n = &st->neurons[st->n_neurons + i];
        n->threshold = threshold;
        n->leak = leak;
        n->refractory_max = refractory;
        n->membrane = 0;
        n->spike = TRIT_UNKNOWN;
    }

    st->n_neurons += n_neurons;
    st->n_layers++;
    return st->n_layers - 1;
}

int snn_connect(snn_state_t *st, int src, int dst, trit weight, int delay) {
    if (!st || !st->initialized) return -1;
    if (src < 0 || src >= st->n_neurons) return -1;
    if (dst < 0 || dst >= st->n_neurons) return -1;
    if (st->n_synapses >= SNN_MAX_SYNAPSES) return -1;

    snn_synapse_t *syn = &st->synapses[st->n_synapses];
    syn->src = src;
    syn->dst = dst;
    syn->weight = weight;
    syn->delay = (delay > 0) ? delay : 1;

    st->n_synapses++;
    return st->n_synapses - 1;
}

/**
 * @brief Set input spikes for external stimulus.
 */
int snn_set_input(snn_state_t *st, int neuron_idx, trit spike) {
    if (!st || !st->initialized) return -1;
    if (neuron_idx < 0 || neuron_idx >= st->n_neurons) return -1;
    st->neurons[neuron_idx].spike = spike;
    return 0;
}

/**
 * @brief Advance the network by one timestep.
 *
 * For each synapse: propagate source spike × weight to destination membrane.
 * For each neuron: apply leak, check threshold, generate spike.
 */
int snn_step(snn_state_t *st) {
    if (!st || !st->initialized) return -1;

    /* Phase 1: Propagate spikes through synapses */
    for (int s = 0; s < st->n_synapses; s++) {
        snn_synapse_t *syn = &st->synapses[s];
        trit src_spike = st->neurons[syn->src].spike;
        if (src_spike == TRIT_UNKNOWN) continue; /* no spike → no effect */

        /* Ternary multiply: spike × weight */
        int contribution = (int)src_spike * (int)syn->weight;
        st->neurons[syn->dst].membrane += contribution;
    }

    /* Phase 2: Update neurons */
    for (int n = 0; n < st->n_neurons; n++) {
        snn_neuron_t *neuron = &st->neurons[n];

        /* Refractory period */
        if (neuron->refractory > 0) {
            neuron->refractory--;
            neuron->spike = TRIT_UNKNOWN;
            continue;
        }

        /* Apply leak */
        if (neuron->membrane > 0)
            neuron->membrane -= neuron->leak;
        else if (neuron->membrane < 0)
            neuron->membrane += neuron->leak;
        if (neuron->membrane > -neuron->leak &&
            neuron->membrane < neuron->leak)
            neuron->membrane = 0;

        /* Threshold check: ternary spike generation */
        if (neuron->membrane >= neuron->threshold) {
            neuron->spike = TRIT_TRUE;   /* excitatory spike */
            neuron->membrane = 0;
            neuron->refractory = neuron->refractory_max;
            neuron->fire_count++;
            st->total_spikes++;
        } else if (neuron->membrane <= -neuron->threshold) {
            neuron->spike = TRIT_FALSE;  /* inhibitory spike */
            neuron->membrane = 0;
            neuron->refractory = neuron->refractory_max;
            neuron->inhibit_count++;
            st->total_inhibits++;
        } else {
            neuron->spike = TRIT_UNKNOWN; /* rest */
        }

        /* Record history */
        neuron->history[neuron->hist_idx % SNN_HISTORY_LEN] = neuron->spike;
        neuron->hist_idx++;
    }

    st->timestep++;
    return 0;
}

/**
 * @brief Get output spike of a neuron.
 */
trit snn_get_output(const snn_state_t *st, int neuron_idx) {
    if (!st || !st->initialized) return TRIT_UNKNOWN;
    if (neuron_idx < 0 || neuron_idx >= st->n_neurons) return TRIT_UNKNOWN;
    return st->neurons[neuron_idx].spike;
}

/**
 * @brief Get firing rate of a neuron (fires / total timesteps).
 */
int snn_get_fire_rate_pct(const snn_state_t *st, int neuron_idx) {
    if (!st || !st->initialized || st->timestep == 0) return 0;
    if (neuron_idx < 0 || neuron_idx >= st->n_neurons) return 0;
    return (st->neurons[neuron_idx].fire_count * 100) / st->timestep;
}
