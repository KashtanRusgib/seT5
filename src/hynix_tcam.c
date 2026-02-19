/**
 * @file hynix_tcam.c
 * @brief Macronix/Hynix US20230162024A1 — TCAM Crossbar for GNN Implementation
 *
 * Software simulation of the Macronix patent's TCAM-based GNN training
 * acceleration system. Implements:
 *
 *   - TCAM crossbar search with hit vector generation
 *   - MAC crossbar feature accumulation
 *   - Dynamic fixed-point encode/decode
 *   - Full GNN training pipeline (sample → aggregate → update)
 *   - Adaptive data reusing with non-uniform bootstrapping
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#include "set5/hynix_tcam.h"
#include <string.h>

/* ==================================================================== */
/*  Internal Helpers                                                    */
/* ==================================================================== */

/**
 * @brief Simple xorshift PRNG for sampling.
 */
static uint32_t tcam_xorshift(uint32_t *seed)
{
    uint32_t x = *seed;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *seed = x;
    return x;
}

/* ==================================================================== */
/*  TCAM Crossbar                                                       */
/* ==================================================================== */

int tcam_crossbar_init(tcam_crossbar_t *tcam)
{
    if (!tcam) return -1;

    memset(tcam, 0, sizeof(*tcam));
    tcam->initialized = 1;

    return 0;
}

int tcam_crossbar_add_edge(tcam_crossbar_t *tcam, int src, int dst,
                           int vtx, int layer)
{
    if (!tcam || !tcam->initialized) return -1;
    if (tcam->row_count >= TCAM_MAX_ROWS) return -1;
    if (src < 0 || dst < 0) return -1;

    int idx = tcam->row_count;
    tcam_entry_t *e = &tcam->entries[idx];

    e->src_node  = src;
    e->dst_node  = dst;
    e->vertex_id = vtx;
    e->layer_id  = layer;
    e->valid     = 1;

    tcam->row_count++;
    return idx;
}

int tcam_crossbar_search_dst(tcam_crossbar_t *tcam, int dst_node,
                             tcam_hit_vector_t *hv)
{
    if (!tcam || !hv || !tcam->initialized) return -1;

    memset(hv, 0, sizeof(*hv));
    hv->length = tcam->row_count;
    hv->hit_count = 0;

    /*
     * Per patent FIG. 7: Search vector = destination node.
     * T-029: Trit-valued hit vector output:
     *   +1 (TRIT_TRUE)   = definite match (dst matches exactly)
     *    0 (TRIT_UNKNOWN) = partial match (invalid/don't-care row)
     *   -1 (TRIT_FALSE)   = no match
     */
    for (int i = 0; i < tcam->row_count; i++) {
        if (!tcam->entries[i].valid) {
            hv->bits[i] = 0;   /* Unknown — row invalid / don't-care */
            continue;
        }

        if (tcam->entries[i].dst_node == dst_node) {
            hv->bits[i] = 1;   /* TRIT_TRUE — definite hit */
            hv->hit_count++;
        } else {
            hv->bits[i] = -1;  /* TRIT_FALSE — no match */
        }
    }

    tcam->searches++;
    tcam->hits += hv->hit_count;

    return hv->hit_count;
}

int tcam_crossbar_search_vtx_layer(tcam_crossbar_t *tcam, int vtx,
                                    int layer, tcam_hit_vector_t *hv)
{
    if (!tcam || !hv || !tcam->initialized) return -1;

    memset(hv, 0, sizeof(*hv));
    hv->length = tcam->row_count;
    hv->hit_count = 0;

    /*
     * Per patent FIG. 9: Search vector = (vertex_id, layer_id).
     * T-029: Trit-valued hit vector — don't-care matches yield UNKNOWN.
     */
    for (int i = 0; i < tcam->row_count; i++) {
        if (!tcam->entries[i].valid) {
            hv->bits[i] = 0;   /* TRIT_UNKNOWN — invalid row */
            continue;
        }

        int vtx_match = (tcam->entries[i].vertex_id == vtx) ||
                        (tcam->entries[i].vertex_id == -1);
        int layer_match = (tcam->entries[i].layer_id == layer) ||
                          (tcam->entries[i].layer_id == -1);

        if (vtx_match && layer_match) {
            hv->bits[i] = 1;   /* TRIT_TRUE — definite hit */
            hv->hit_count++;
        } else {
            hv->bits[i] = -1;  /* TRIT_FALSE — no match */
        }
    }

    tcam->searches++;
    tcam->hits += hv->hit_count;

    return hv->hit_count;
}

/* ==================================================================== */
/*  MAC Crossbar                                                        */
/* ==================================================================== */

int mac_crossbar_init(mac_crossbar_t *mac)
{
    if (!mac) return -1;

    memset(mac, 0, sizeof(*mac));
    mac->initialized = 1;

    return 0;
}

int mac_crossbar_add_features(mac_crossbar_t *mac, const int *feats, int dim)
{
    if (!mac || !feats || !mac->initialized) return -1;
    if (mac->row_count >= TCAM_MAX_ROWS) return -1;
    if (dim <= 0 || dim > TCAM_MAX_FEATURES) return -1;

    int idx = mac->row_count;
    mac_feature_t *f = &mac->features[idx];

    for (int i = 0; i < dim; i++) {
        f->features[i] = feats[i];
    }
    f->dim = dim;
    f->valid = 1;

    mac->row_count++;
    return idx;
}

int mac_crossbar_accumulate(mac_crossbar_t *mac, const tcam_hit_vector_t *hv,
                            int *result, int dim)
{
    if (!mac || !hv || !result || !mac->initialized) return -1;
    if (dim <= 0 || dim > TCAM_MAX_FEATURES) return -1;

    /*
     * Per patent FIG. 7: for each row where HV[i] == 1,
     * accumulate (add) the feature vector into the result.
     *
     * result = Σ features[i]  where HV[i] == 1
     *
     * This is the "aggregation" step of the GNN pipeline.
     */
    for (int d = 0; d < dim; d++) {
        result[d] = 0;
    }

    for (int i = 0; i < hv->length && i < mac->row_count; i++) {
        if (hv->bits[i] != 1) continue;
        if (!mac->features[i].valid) continue;

        for (int d = 0; d < dim && d < mac->features[i].dim; d++) {
            result[d] += mac->features[i].features[d];
        }
        mac->mac_ops++;
    }

    return 0;
}

/* ==================================================================== */
/*  Dynamic Fixed-Point                                                 */
/* ==================================================================== */

int tcam_dfp_encode(int mantissa, int exponent, tcam_dfp_value_t *out)
{
    if (!out) return -1;

    /*
     * Per patent FIG. 15 and Table I:
     *   Exponent range: 2^-0 to 2^-7
     *   Group G0: 2^-0 to 2^-3  (exponents 0 to -3)
     *   Group G1: 2^-4 to 2^-7  (exponents -4 to -7)
     *
     * Within each group, the mantissa is shifted by the offset
     * within that group (0..3 positions).
     */
    int abs_exp = exponent < 0 ? -exponent : exponent;

    if (abs_exp <= 3) {
        /* Group G0: exponents 0 to -3 */
        out->group = 0;
        out->shift = abs_exp;
    } else if (abs_exp <= 7) {
        /* Group G1: exponents -4 to -7 */
        out->group = 1;
        out->shift = abs_exp - 4;
    } else {
        /* Out of range — clamp to group 1 */
        out->group = 1;
        out->shift = 3;
    }

    /* Shift mantissa according to position within group */
    out->mantissa = (mantissa & 0xFF) >> out->shift;

    return 0;
}

int tcam_dfp_decode(const tcam_dfp_value_t *dfp)
{
    if (!dfp) return 0;

    /*
     * Reconstruct value from DFP representation.
     * The shift represents lost precision; shift back to approximate.
     * The group adds a base exponent offset:
     *   G0: base = 0, G1: base = 4
     */
    int base_exp = dfp->group * 4 + dfp->shift;
    int value = dfp->mantissa << dfp->shift;

    /* Apply group-level scaling (rough approximation for simulation) */
    if (dfp->group == 1) {
        /* Group 1 values are ~16× smaller (2^-4 base) */
        value = value >> 4;
    }

    (void)base_exp; /* Used implicitly through the shift */
    return value;
}

int tcam_dfp_mac(const tcam_dfp_value_t *a, const tcam_dfp_value_t *b,
                 int count)
{
    if (!a || !b || count <= 0) return 0;

    /*
     * Per patent: DFP MAC groups operations by exponent group.
     * Group 0 products and Group 1 products are accumulated separately,
     * then combined. This reduces cycles from 7 to 2.
     */
    int acc_g0 = 0;
    int acc_g1 = 0;

    for (int i = 0; i < count; i++) {
        int va = tcam_dfp_decode(&a[i]);
        int vb = tcam_dfp_decode(&b[i]);
        int product = va * vb;

        /* Classify accumulation by combined group */
        if (a[i].group == 0 && b[i].group == 0) {
            acc_g0 += product;
        } else {
            acc_g1 += product;
        }
    }

    /* Combine: G1 products are scaled down */
    return acc_g0 + acc_g1;
}

/* ==================================================================== */
/*  GNN Training Pipeline                                               */
/* ==================================================================== */

int tcam_gnn_init(tcam_gnn_state_t *state)
{
    if (!state) return -1;

    memset(state, 0, sizeof(*state));

    /* Initialize sub-components */
    tcam_crossbar_init(&state->tcam);
    mac_crossbar_init(&state->mac);

    state->initialized = 1;
    return 0;
}

int tcam_gnn_load_graph(tcam_gnn_state_t *state, const tcam_graph_t *graph)
{
    if (!state || !graph || !state->initialized) return -1;
    if (graph->edge_count > TCAM_MAX_EDGES) return -1;
    if (graph->node_count > TCAM_MAX_NODES) return -1;

    /* Copy graph data */
    state->graph = *graph;

    /* Reset crossbars */
    tcam_crossbar_init(&state->tcam);
    mac_crossbar_init(&state->mac);

    /*
     * Populate TCAM crossbar with graph edges.
     * Each edge becomes one TCAM row with (src, dst, vertex=0, layer=0).
     */
    for (int i = 0; i < graph->edge_count; i++) {
        if (tcam_crossbar_add_edge(&state->tcam,
                                    graph->edge_src[i],
                                    graph->edge_dst[i],
                                    0, 0) < 0) {
            return -1;
        }

        /*
         * Populate MAC crossbar with features of the source node.
         * Per patent: MAC stores features corresponding to each edge's
         * source node.
         */
        int src = graph->edge_src[i];
        if (src >= 0 && src < graph->node_count) {
            if (mac_crossbar_add_features(&state->mac,
                                           graph->node_features[src],
                                           graph->feature_dim) < 0) {
                return -1;
            }
        }
    }

    /* Initialize weights to identity-like (for first epoch) */
    state->weight_dim = graph->feature_dim;
    for (int i = 0; i < graph->feature_dim && i < TCAM_MAX_FEATURES; i++) {
        for (int j = 0; j < graph->feature_dim && j < TCAM_MAX_FEATURES; j++) {
            state->weights[i][j] = (i == j) ? 1 : 0;
        }
    }

    return 0;
}

int tcam_gnn_sample_batch(tcam_gnn_state_t *state, int batch_size,
                          uint32_t seed)
{
    if (!state || !state->initialized) return -1;
    if (batch_size <= 0 || batch_size > TCAM_MAX_BATCH) return -1;
    if (state->graph.node_count == 0) return -1;

    int n = state->graph.node_count;
    state->batch_size = 0;

    /*
     * Per patent FIG. 16: Bootstrapping approach.
     * Some nodes are repeated across batches for data reuse.
     * Per patent FIG. 18: Non-uniform sampling reduces probability
     * for over-sampled nodes.
     */
    for (int i = 0; i < batch_size && state->batch_size < TCAM_MAX_BATCH; i++) {
        /* Generate random node index */
        int node_id = (int)(tcam_xorshift(&seed) % (uint32_t)n);

        /*
         * Non-uniform bootstrapping: if a node has been sampled
         * too many times (> 2× average), give it 50% chance of
         * being skipped (replaced by next random node).
         */
        int avg_samples = (state->batches_processed + 1);
        if (state->sample_counts[node_id] > avg_samples * 2) {
            /* 50% chance to skip */
            if (tcam_xorshift(&seed) & 1) {
                node_id = (int)(tcam_xorshift(&seed) % (uint32_t)n);
            }
        }

        state->batch_nodes[state->batch_size] = node_id;
        state->sample_counts[node_id]++;
        state->batch_size++;
    }

    return state->batch_size;
}

int tcam_gnn_aggregate(tcam_gnn_state_t *state)
{
    if (!state || !state->initialized) return -1;
    if (state->batch_size == 0) return -1;

    int dim = state->graph.feature_dim;
    int aggregated_count = 0;

    /*
     * Per patent FIG. 7-10: For each node in the batch:
     *   1. Search TCAM by destination node → hit vector
     *   2. Feed hit vector to MAC crossbar → accumulated features
     *   3. Store aggregated features for update phase
     */
    for (int b = 0; b < state->batch_size; b++) {
        int node_id = state->batch_nodes[b];
        tcam_hit_vector_t hv;

        /* TCAM search for edges pointing to this node */
        int hits = tcam_crossbar_search_dst(&state->tcam, node_id, &hv);
        if (hits < 0) continue;

        /* MAC accumulation */
        int result[TCAM_MAX_FEATURES];
        memset(result, 0, sizeof(result));

        if (hv.hit_count > 0) {
            if (mac_crossbar_accumulate(&state->mac, &hv, result, dim) < 0)
                continue;
        }

        /*
         * Add self-features (per most GNN architectures).
         * aggregated[node] = self_features + Σ neighbor_features
         */
        if (node_id >= 0 && node_id < state->graph.node_count) {
            for (int d = 0; d < dim; d++) {
                state->aggregated[node_id][d] =
                    state->graph.node_features[node_id][d] + result[d];
            }
        }

        state->total_aggregations++;
        aggregated_count++;
    }

    return aggregated_count;
}

int tcam_gnn_update(tcam_gnn_state_t *state)
{
    if (!state || !state->initialized) return -1;

    int dim = state->graph.feature_dim;

    /*
     * Per patent: Update phase applies weight matrix to aggregated features.
     * For each node in the batch:
     *   new_features[node] = weights × aggregated[node]
     *
     * This is a simplified linear transform (no activation function in
     * this simulation, but the pipeline is extensible).
     */
    for (int b = 0; b < state->batch_size; b++) {
        int node_id = state->batch_nodes[b];
        if (node_id < 0 || node_id >= state->graph.node_count) continue;

        int temp[TCAM_MAX_FEATURES];
        memset(temp, 0, sizeof(temp));

        /* Matrix-vector multiply: temp = weights × aggregated[node] */
        for (int i = 0; i < dim && i < TCAM_MAX_FEATURES; i++) {
            for (int j = 0; j < dim && j < TCAM_MAX_FEATURES; j++) {
                temp[i] += state->weights[i][j] *
                           state->aggregated[node_id][j];
            }
        }

        /* Write back to aggregated (in-place update) */
        for (int i = 0; i < dim; i++) {
            state->aggregated[node_id][i] = temp[i];
        }

        state->total_mac_ops += dim * dim;
    }

    return 0;
}

int tcam_gnn_train_epoch(tcam_gnn_state_t *state, uint32_t seed)
{
    if (!state || !state->initialized) return -1;

    /* 1. Sample batch */
    int batch = state->graph.node_count;
    if (batch > TCAM_MAX_BATCH) batch = TCAM_MAX_BATCH;
    if (tcam_gnn_sample_batch(state, batch, seed) < 0) return -1;

    /* 2. Aggregate */
    if (tcam_gnn_aggregate(state) < 0) return -1;

    /* 3. Update */
    if (tcam_gnn_update(state) < 0) return -1;

    state->epochs_completed++;
    state->batches_processed++;

    return 0;
}

int tcam_gnn_get_node_features(const tcam_gnn_state_t *state, int node_id,
                               int *out, int dim)
{
    if (!state || !out || !state->initialized) return -1;
    if (node_id < 0 || node_id >= state->graph.node_count) return -1;
    if (dim <= 0 || dim > TCAM_MAX_FEATURES) return -1;

    for (int i = 0; i < dim; i++) {
        out[i] = state->aggregated[node_id][i];
    }

    return 0;
}
