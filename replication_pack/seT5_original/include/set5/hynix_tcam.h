/**
 * @file hynix_tcam.h
 * @brief Macronix/Hynix US20230162024A1 — TCAM Crossbar for GNN Interface
 *
 * Software model of the Macronix patent describing a Ternary Content
 * Addressable Memory (TCAM)-based system for Graph Neural Network training:
 *
 *   - TCAM crossbar matrix: Stores graph edges, searches by vertex,
 *     outputs hit vectors for neighbor selection.
 *   - MAC (Multiply Accumulate) crossbar: Stores node features,
 *     performs aggregation weighted by the TCAM hit vector.
 *   - GNN pipeline: Feature extraction → Aggregation → Update phases.
 *   - Dynamic fixed-point formatting: Reduces exponent range from 7
 *     groups to 2 for 3.5× speedup.
 *   - Adaptive data reusing: Bootstrapping, graph partitioning, and
 *     non-uniform sampling policies.
 *
 * Integration with seT5:
 *   - Uses balanced ternary trits for TCAM match/don't-care/mismatch:
 *       +1 = match, 0 = don't-care, -1 = mismatch
 *   - Compatible with ternary AI subsystem (trit_ai.{h,c})
 *   - Leverages Kleene logic for "unknown" (don't-care) states
 *
 * The seT5 microkernel is NOT modified.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

#ifndef SET5_HYNIX_TCAM_H
#define SET5_HYNIX_TCAM_H

#include "set5/trit.h"
#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==================================================================== */
/*  Constants                                                           */
/* ==================================================================== */

/** Maximum rows in a TCAM crossbar matrix (edges stored) */
#define TCAM_MAX_ROWS           64

/** Maximum columns (bit width of each entry) */
#define TCAM_MAX_COLS           32

/** Maximum nodes in the GNN graph */
#define TCAM_MAX_NODES          128

/** Maximum edges in the GNN graph */
#define TCAM_MAX_EDGES          256

/** Maximum feature dimensions per node */
#define TCAM_MAX_FEATURES       16

/** Dynamic fixed-point: number of exponent groups (per patent: 2) */
#define TCAM_DFP_GROUPS         2

/** Maximum batch size for training */
#define TCAM_MAX_BATCH          32

/* ==================================================================== */
/*  TCAM Entry                                                          */
/* ==================================================================== */

/**
 * @brief A single TCAM crossbar row (edge storage).
 *
 * Per patent FIG. 6: each row stores source node, destination node,
 * and optionally vertex ID + layer ID.
 *
 * TCAM matching semantics (ternary):
 *   +1 (match required), 0 (don't care), -1 (inverse match)
 */
typedef struct {
    int   src_node;            /**< Source node ID                     */
    int   dst_node;            /**< Destination node ID                */
    int   vertex_id;           /**< Vertex group ID (-1 = any)         */
    int   layer_id;            /**< GNN layer ID (-1 = any)            */
    int   valid;               /**< 1 = entry is active                */
} tcam_entry_t;

/* ==================================================================== */
/*  TCAM Crossbar Matrix                                                */
/* ==================================================================== */

/**
 * @brief TCAM crossbar matrix for graph edge storage and lookup.
 *
 * Per patent FIG. 6: TCAM stores edges as rows; a search vector
 * (vertex + layer) produces a hit vector selecting matching edges.
 */
typedef struct {
    tcam_entry_t  entries[TCAM_MAX_ROWS];  /**< TCAM rows (edges)     */
    int           row_count;     /**< Number of active rows             */
    int           searches;      /**< Total search operations           */
    int           hits;          /**< Total matching rows found         */
    int           initialized;   /**< 1 = ready for operations          */
} tcam_crossbar_t;

/* ==================================================================== */
/*  MAC Crossbar Matrix                                                 */
/* ==================================================================== */

/**
 * @brief Feature storage entry for the MAC crossbar.
 *
 * Per patent FIG. 6: each row in the MAC crossbar stores features
 * corresponding to one edge in the TCAM.
 */
typedef struct {
    int   features[TCAM_MAX_FEATURES]; /**< Feature vector (fixed-pt)  */
    int   dim;                 /**< Number of active dimensions         */
    int   valid;               /**< 1 = entry is active                 */
} mac_feature_t;

/**
 * @brief MAC (Multiply-Accumulate) crossbar matrix.
 *
 * Stores node features and performs weighted accumulation
 * using the hit vector from the TCAM crossbar.
 */
typedef struct {
    mac_feature_t features[TCAM_MAX_ROWS]; /**< Feature rows           */
    int           row_count;     /**< Number of active feature rows     */
    int           mac_ops;       /**< Total MAC operations performed    */
    int           initialized;   /**< 1 = ready for operations          */
} mac_crossbar_t;

/* ==================================================================== */
/*  Hit Vector                                                          */
/* ==================================================================== */

/**
 * @brief Hit vector produced by TCAM search.
 *
 * Binary vector: 1 = matching row, 0 = non-matching row.
 * Used to gate the MAC crossbar's accumulation.
 */
typedef struct {
    int   bits[TCAM_MAX_ROWS]; /**< 1=hit, 0=miss per row              */
    int   length;              /**< Number of valid bits                */
    int   hit_count;           /**< Number of 1s in the vector          */
} tcam_hit_vector_t;

/* ==================================================================== */
/*  Dynamic Fixed-Point Format                                          */
/* ==================================================================== */

/**
 * @brief Dynamic fixed-point representation per patent FIG. 15.
 *
 * Floating-point values are converted to fixed-point with the
 * exponent classified into 2 groups. The mantissa is shifted
 * according to the exponent's position within its group.
 *
 * This reduces computation from 7 exponent cycles to 2.
 */
typedef struct {
    int   mantissa;            /**< Shifted mantissa (8-bit)            */
    int   group;               /**< Exponent group: 0 or 1             */
    int   shift;               /**< Mantissa shift within group (0-3)  */
} tcam_dfp_value_t;

/* ==================================================================== */
/*  GNN Training State                                                  */
/* ==================================================================== */

/**
 * @brief Graph structure for GNN training.
 *
 * Simple adjacency list representation with node features.
 */
typedef struct {
    int   edge_src[TCAM_MAX_EDGES];     /**< Edge source nodes         */
    int   edge_dst[TCAM_MAX_EDGES];     /**< Edge destination nodes    */
    int   edge_count;                    /**< Number of edges           */
    int   node_count;                    /**< Number of nodes           */
    int   node_features[TCAM_MAX_NODES][TCAM_MAX_FEATURES]; /**< Features */
    int   feature_dim;                   /**< Feature dimensionality    */
} tcam_graph_t;

/**
 * @brief GNN training pipeline state.
 *
 * Per patent FIG. 2: Sampling → Feature extraction → Aggregation → Update
 */
typedef struct {
    tcam_crossbar_t  tcam;          /**< TCAM crossbar for edges       */
    mac_crossbar_t   mac;           /**< MAC crossbar for features     */
    tcam_graph_t     graph;         /**< Graph data                    */

    /* Aggregation results (per node) */
    int   aggregated[TCAM_MAX_NODES][TCAM_MAX_FEATURES];

    /* Weights for update phase */
    int   weights[TCAM_MAX_FEATURES][TCAM_MAX_FEATURES];
    int   weight_dim;

    /* Training statistics */
    int   epochs_completed;
    int   batches_processed;
    int   total_aggregations;
    int   total_mac_ops;

    /* Sampling state */
    int   sample_counts[TCAM_MAX_NODES]; /**< Per-node sample frequency */
    int   batch_nodes[TCAM_MAX_BATCH];   /**< Current batch node IDs    */
    int   batch_size;

    int   initialized;
} tcam_gnn_state_t;

/* ==================================================================== */
/*  API — TCAM Crossbar Operations                                      */
/* ==================================================================== */

/**
 * @brief Initialize a TCAM crossbar matrix.
 */
int tcam_crossbar_init(tcam_crossbar_t *tcam);

/**
 * @brief Add an edge entry to the TCAM crossbar.
 *
 * @param src  Source node ID
 * @param dst  Destination node ID
 * @param vtx  Vertex group ID (-1 for don't-care)
 * @param layer GNN layer ID (-1 for don't-care)
 * @return Row index on success, -1 on error
 */
int tcam_crossbar_add_edge(tcam_crossbar_t *tcam, int src, int dst,
                           int vtx, int layer);

/**
 * @brief Search TCAM by destination node — produce a hit vector.
 *
 * Per patent FIG. 7: search vector contains the target destination
 * node. Matching rows produce HV=1; non-matching produce HV=0.
 *
 * @param tcam      TCAM crossbar to search
 * @param dst_node  Target destination node
 * @param hv        Output hit vector
 * @return Number of hits, or -1 on error
 */
int tcam_crossbar_search_dst(tcam_crossbar_t *tcam, int dst_node,
                             tcam_hit_vector_t *hv);

/**
 * @brief Search TCAM by vertex and layer — produce a hit vector.
 *
 * Per patent FIG. 9: search for a specific (vertex, layer) pair.
 */
int tcam_crossbar_search_vtx_layer(tcam_crossbar_t *tcam, int vtx,
                                    int layer, tcam_hit_vector_t *hv);

/* ==================================================================== */
/*  API — MAC Crossbar Operations                                       */
/* ==================================================================== */

/**
 * @brief Initialize a MAC crossbar matrix.
 */
int mac_crossbar_init(mac_crossbar_t *mac);

/**
 * @brief Add a feature row to the MAC crossbar.
 *
 * @param feats  Feature vector
 * @param dim    Number of feature dimensions
 * @return Row index on success, -1 on error
 */
int mac_crossbar_add_features(mac_crossbar_t *mac, const int *feats, int dim);

/**
 * @brief Perform multiply-accumulate using a hit vector.
 *
 * Sums all feature rows where the hit vector is 1.
 * Per patent FIG. 7: result = Σ (features[i] where HV[i] == 1).
 *
 * @param mac    MAC crossbar
 * @param hv     Hit vector from TCAM search
 * @param result Output feature vector (accumulated)
 * @param dim    Feature dimension
 * @return 0 on success, -1 on error
 */
int mac_crossbar_accumulate(mac_crossbar_t *mac, const tcam_hit_vector_t *hv,
                            int *result, int dim);

/* ==================================================================== */
/*  API — Dynamic Fixed-Point                                           */
/* ==================================================================== */

/**
 * @brief Convert a floating-point-like integer to dynamic fixed-point.
 *
 * Per patent Table I and FIG. 15: classify exponent into group 0 or 1,
 * shift mantissa accordingly.
 *
 * @param mantissa  8-bit mantissa
 * @param exponent  Exponent (0 to -7)
 * @param out       Output DFP value
 * @return 0 on success, -1 on error
 */
int tcam_dfp_encode(int mantissa, int exponent, tcam_dfp_value_t *out);

/**
 * @brief Decode a dynamic fixed-point value back to integer.
 *
 * @param dfp  DFP value
 * @return Decoded integer representation
 */
int tcam_dfp_decode(const tcam_dfp_value_t *dfp);

/**
 * @brief Perform DFP multiply-accumulate on two arrays.
 *
 * @param a     First DFP array
 * @param b     Second DFP array
 * @param count Number of elements
 * @return Accumulated result
 */
int tcam_dfp_mac(const tcam_dfp_value_t *a, const tcam_dfp_value_t *b,
                 int count);

/* ==================================================================== */
/*  API — GNN Training Pipeline                                         */
/* ==================================================================== */

/**
 * @brief Initialize the GNN training pipeline.
 */
int tcam_gnn_init(tcam_gnn_state_t *state);

/**
 * @brief Load a graph into the pipeline (nodes + edges + features).
 *
 * Populates the TCAM and MAC crossbars from the graph structure.
 */
int tcam_gnn_load_graph(tcam_gnn_state_t *state, const tcam_graph_t *graph);

/**
 * @brief Sample a batch of nodes for training.
 *
 * Implements the adaptive data reusing policy:
 *   - Bootstrapping: some nodes repeated across batches
 *   - Non-uniform sampling: reduce over-sampled nodes
 *
 * @param state      GNN state
 * @param batch_size Number of nodes to sample
 * @param seed       PRNG seed for reproducibility
 * @return Number of nodes sampled
 */
int tcam_gnn_sample_batch(tcam_gnn_state_t *state, int batch_size,
                          uint32_t seed);

/**
 * @brief Execute the aggregation phase for a batch.
 *
 * For each node in the batch:
 *   1. Search TCAM for edges pointing to this node
 *   2. Get hit vector
 *   3. MAC accumulate neighbor features
 *   4. Store aggregated result
 *
 * @return Number of nodes aggregated, or -1 on error
 */
int tcam_gnn_aggregate(tcam_gnn_state_t *state);

/**
 * @brief Execute the update phase — apply weights to aggregated features.
 *
 * Per patent: updated_feature = weights × aggregated_feature
 *
 * @return 0 on success, -1 on error
 */
int tcam_gnn_update(tcam_gnn_state_t *state);

/**
 * @brief Run one complete training epoch (sample → aggregate → update).
 *
 * @param seed  PRNG seed for batch sampling
 * @return 0 on success, -1 on error
 */
int tcam_gnn_train_epoch(tcam_gnn_state_t *state, uint32_t seed);

/**
 * @brief Get the aggregated feature vector for a specific node.
 *
 * @param state    GNN state
 * @param node_id  Node ID
 * @param out      Output feature buffer
 * @param dim      Feature dimension
 * @return 0 on success, -1 on error
 */
int tcam_gnn_get_node_features(const tcam_gnn_state_t *state, int node_id,
                               int *out, int dim);

#ifdef __cplusplus
}
#endif

#endif /* SET5_HYNIX_TCAM_H */
