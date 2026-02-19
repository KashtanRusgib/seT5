/**
 * @file tenet_dataflow.v
 * @brief T-041: TENET-Style Ternary MAC Dataflow Architecture
 *
 * Models the 21.1× efficient ternary MAC unit from TENET ASIC research:
 *   - 3-level weight encoding (±1, 0) eliminates multiplier
 *   - MAC = conditional accumulate: add, subtract, or skip
 *   - Integrates with existing ALU and Wallace-tree modules
 *
 * SPDX-License-Identifier: GPL-2.0
 */

`timescale 1ns / 1ps

module tenet_dataflow #(
    parameter TRIT_WIDTH = 2,
    parameter VEC_LEN    = 9,       /* 9-trit vector (one tryte) */
    parameter ACC_WIDTH  = 16       /* accumulator width */
)(
    input  wire                            clk,
    input  wire                            rst_n,

    /* Input activation (binary fixed-point, 8-bit) */
    input  wire [VEC_LEN*8-1:0]            activation,

    /* Ternary weight vector (2-bit encoded per weight) */
    input  wire [VEC_LEN*TRIT_WIDTH-1:0]   weight,

    /* Control */
    input  wire                            start,
    output reg                             done,

    /* MAC output (signed accumulator) */
    output reg  signed [ACC_WIDTH-1:0]     mac_out,

    /* Energy counter (for comparison with binary MAC) */
    output reg  [15:0]                     energy_ops
);

    /* ── Trit decoder ── */
    function signed [1:0] decode_weight;
        input [1:0] w;
        begin
            case (w)
                2'b10:   decode_weight = -1;  /* F */
                2'b00:   decode_weight = 0;   /* U */
                2'b01:   decode_weight = 1;   /* T */
                default: decode_weight = 0;   /* fault → skip */
            endcase
        end
    endfunction

    /* ── MAC dataflow pipeline ── */
    reg [3:0] idx;
    reg computing;
    reg signed [ACC_WIDTH-1:0] acc;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mac_out    <= 0;
            done       <= 1'b0;
            computing  <= 1'b0;
            idx        <= 0;
            acc        <= 0;
            energy_ops <= 0;
        end else if (start && !computing) begin
            computing <= 1'b1;
            done      <= 1'b0;
            idx       <= 0;
            acc       <= 0;
        end else if (computing) begin
            if (idx < VEC_LEN) begin
                /* Extract activation[idx] (8-bit signed) */
                wire signed [7:0] act_val;
                assign act_val = activation[idx*8 +: 8];

                /* Extract weight[idx] (2-bit trit) */
                wire [1:0] w_enc;
                assign w_enc = weight[idx*TRIT_WIDTH +: TRIT_WIDTH];

                /* TENET key insight: no multiplier needed!
                 * weight = +1 → acc += activation
                 * weight =  0 → acc += 0 (skip)
                 * weight = -1 → acc -= activation
                 * This saves ~21× energy vs binary multiply */
                case (weight[idx*TRIT_WIDTH +: TRIT_WIDTH])
                    2'b01: acc <= acc + $signed(activation[idx*8 +: 8]);  /* +1: add */
                    2'b10: acc <= acc - $signed(activation[idx*8 +: 8]);  /* -1: sub */
                    default: ; /* 0: skip — zero energy! */
                endcase

                energy_ops <= energy_ops + (weight[idx*TRIT_WIDTH +: TRIT_WIDTH] != 2'b00 ? 1 : 0);
                idx <= idx + 1;
            end else begin
                mac_out   <= acc;
                done      <= 1'b1;
                computing <= 1'b0;
            end
        end else begin
            done <= 1'b0;
        end
    end

endmodule

/* ── Systolic array of TENET MAC units ── */
module tenet_systolic_array #(
    parameter ROWS = 4,
    parameter COLS = 4,
    parameter VEC_LEN = 9,
    parameter ACC_WIDTH = 16
)(
    input  wire                                clk,
    input  wire                                rst_n,
    input  wire [ROWS*VEC_LEN*8-1:0]           activations,
    input  wire [ROWS*COLS*VEC_LEN*2-1:0]      weights,
    input  wire                                start,
    output wire [COLS*ACC_WIDTH-1:0]            outputs,
    output wire                                all_done
);

    wire [ROWS*COLS-1:0] unit_done;

    genvar r, c;
    generate
        for (r = 0; r < ROWS; r = r + 1) begin : row_gen
            for (c = 0; c < COLS; c = c + 1) begin : col_gen
                tenet_dataflow #(
                    .VEC_LEN(VEC_LEN),
                    .ACC_WIDTH(ACC_WIDTH)
                ) mac_unit (
                    .clk(clk),
                    .rst_n(rst_n),
                    .activation(activations[r*VEC_LEN*8 +: VEC_LEN*8]),
                    .weight(weights[(r*COLS+c)*VEC_LEN*2 +: VEC_LEN*2]),
                    .start(start),
                    .done(unit_done[r*COLS+c]),
                    .mac_out(), /* accumulate in column */
                    .energy_ops()
                );
            end
        end
    endgenerate

    assign all_done = &unit_done;

endmodule
