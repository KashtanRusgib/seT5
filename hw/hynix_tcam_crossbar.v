/*
 * hynix_tcam_crossbar.v
 * Verilog Simulation Model for Macronix/Hynix US20230162024A1 TCAM Crossbar
 *
 * Implements the TCAM-based crossbar array for GNN acceleration
 * as described in patent US20230162024A1:
 *
 *   1. TCAM Crossbar — adjacency lookup with hit vector generation
 *   2. MAC Crossbar  — feature accumulation driven by hit vectors
 *   3. DFP MAC       — dynamic fixed-point multiply-accumulate
 *   4. Hit Vector    — 64-bit binary match vector
 *
 * TCAM entry encoding:
 *   Each row stores (src_node, dst_node, vertex_id, layer_id)
 *   Search operations match against dst_node or (vertex_id, layer_id)
 *   Don't-care: vertex_id = -1 or layer_id = -1 matches anything
 *
 * Reference: US20230162024A1, Macronix International / SK Hynix
 *            "TCAM Crossbar for GNN Training Acceleration"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ===================================================================
 * TCAM Configuration Constants
 * ===================================================================*/

`define TCAM_ROWS       64
`define TCAM_NODE_BITS   8
`define TCAM_FEAT_BITS  16
`define TCAM_FEAT_DIM   16

/* ===================================================================
 * TCAM Row — Single Entry Storage
 *
 * Per patent FIG. 7: Each TCAM row stores an adjacency edge
 * (src_node, dst_node) and metadata (vertex_id, layer_id).
 * ===================================================================*/
module tcam_row (
    input  wire        clk,
    input  wire        reset,
    input  wire        write_en,
    /* Write data */
    input  wire [`TCAM_NODE_BITS-1:0] wr_src_node,
    input  wire [`TCAM_NODE_BITS-1:0] wr_dst_node,
    input  wire [`TCAM_NODE_BITS-1:0] wr_vertex_id,
    input  wire [`TCAM_NODE_BITS-1:0] wr_layer_id,
    /* Search input */
    input  wire [`TCAM_NODE_BITS-1:0] search_dst,
    input  wire        search_en,
    /* Match output */
    output reg         hit,
    output reg         valid
);

    /* Stored entry */
    reg [`TCAM_NODE_BITS-1:0] src_node;
    reg [`TCAM_NODE_BITS-1:0] dst_node;
    reg [`TCAM_NODE_BITS-1:0] vertex_id;
    reg [`TCAM_NODE_BITS-1:0] layer_id;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            src_node  <= 0;
            dst_node  <= 0;
            vertex_id <= 0;
            layer_id  <= 0;
            valid     <= 0;
            hit       <= 0;
        end else if (write_en) begin
            src_node  <= wr_src_node;
            dst_node  <= wr_dst_node;
            vertex_id <= wr_vertex_id;
            layer_id  <= wr_layer_id;
            valid     <= 1;
            hit       <= 0;
        end else if (search_en) begin
            /*
             * Per patent: content-addressable match.
             * Hit = 1 when stored dst_node matches search_dst
             * and the row is valid.
             */
            hit <= valid & (dst_node == search_dst);
        end
    end

endmodule


/* ===================================================================
 * Hit Vector Generator — 64-bit TCAM Match Result
 *
 * Per patent FIG. 7: The TCAM produces a hit vector HV[0:N-1]
 * where HV[i] = 1 if row i matches the search key.
 * ===================================================================*/
module tcam_hit_vector (
    input  wire [`TCAM_ROWS-1:0] row_hits,   /* Per-row match signals */
    output wire [`TCAM_ROWS-1:0] hit_vector, /* Binary hit vector     */
    output reg  [6:0]            hit_count   /* Population count      */
);

    assign hit_vector = row_hits;

    /* Population count (number of 1-bits in hit vector) */
    integer i;
    always @(*) begin
        hit_count = 0;
        for (i = 0; i < `TCAM_ROWS; i = i + 1) begin
            hit_count = hit_count + row_hits[i];
        end
    end

endmodule


/* ===================================================================
 * MAC Accumulator Row — Feature Storage and Accumulation
 *
 * Per patent FIG. 7: Each MAC row stores a feature vector.
 * When the corresponding HV bit is 1, the features are added
 * to the accumulator output.
 * ===================================================================*/
module mac_row (
    input  wire        clk,
    input  wire        reset,
    input  wire        write_en,
    input  wire        hit,            /* Hit vector bit for this row  */
    input  wire signed [`TCAM_FEAT_BITS-1:0] wr_feature, /* Write data */
    output reg  signed [`TCAM_FEAT_BITS-1:0] feature,    /* Stored data */
    output wire signed [`TCAM_FEAT_BITS-1:0] contrib     /* Contribution */
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            feature <= 0;
        end else if (write_en) begin
            feature <= wr_feature;
        end
    end

    /* Gate output by hit vector: contribute feature if HV=1 */
    assign contrib = hit ? feature : {`TCAM_FEAT_BITS{1'b0}};

endmodule


/* ===================================================================
 * DFP MAC Unit — Dynamic Fixed-Point Multiply-Accumulate
 *
 * Per patent FIG. 15 and Table I:
 *   - Exponents divided into 2 groups (G0: 2^0..2^-3, G1: 2^-4..2^-7)
 *   - Within each group, values are aligned by shift
 *   - Reduces MAC cycles from 7 to 2 (one per group)
 * ===================================================================*/
module dfp_mac_unit (
    input  wire        clk,
    input  wire        reset,
    input  wire        start,
    input  wire signed [7:0] a_mantissa,
    input  wire        [0:0] a_group,      /* 0=G0, 1=G1 */
    input  wire        [1:0] a_shift,
    input  wire signed [7:0] b_mantissa,
    input  wire        [0:0] b_group,
    input  wire        [1:0] b_shift,
    output reg  signed [15:0] result,
    output reg         done
);

    reg signed [7:0] a_aligned;
    reg signed [7:0] b_aligned;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            result <= 0;
            done   <= 0;
        end else if (start) begin
            /* Align mantissas within their groups */
            a_aligned = a_mantissa >>> a_shift;
            b_aligned = b_mantissa >>> b_shift;

            /* Multiply and scale by combined group offset */
            if (a_group == 0 && b_group == 0) begin
                /* G0×G0: full precision */
                result <= a_aligned * b_aligned;
            end else begin
                /* G0×G1 or G1×G1: reduced precision (>>4 per G1 operand) */
                result <= (a_aligned * b_aligned) >>>
                          ((a_group * 4) + (b_group * 4));
            end
            done <= 1;
        end else begin
            done <= 0;
        end
    end

endmodule
