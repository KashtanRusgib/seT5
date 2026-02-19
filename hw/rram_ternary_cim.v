/**
 * @file rram_ternary_cim.v
 * @brief T-033: RRAM Ternary Compute-in-Memory Crossbar — Verilog Model
 *
 * Hardware model of an RRAM crossbar array with ternary cells.
 * Each cell stores one trit (2-bit encoded). MAC operation is
 * parallel column current summation.
 *
 * SPDX-License-Identifier: GPL-2.0
 */

`timescale 1ns / 1ps

module rram_ternary_cim #(
    parameter ROWS = 16,
    parameter COLS = 16,
    parameter TRIT_WIDTH = 2    /* 2-bit encoding per trit */
)(
    input  wire                        clk,
    input  wire                        rst_n,

    /* Write interface */
    input  wire [$clog2(ROWS)-1:0]     wr_row,
    input  wire [$clog2(COLS)-1:0]     wr_col,
    input  wire [TRIT_WIDTH-1:0]       wr_data,   /* 10=F, 00=U, 01=T */
    input  wire                        wr_en,

    /* MAC interface */
    input  wire [ROWS*TRIT_WIDTH-1:0]  input_vector,  /* ternary input */
    input  wire                        mac_start,
    output reg  [COLS*8-1:0]           mac_result,    /* signed 8-bit per col */
    output reg                         mac_done,

    /* Read interface */
    input  wire [$clog2(ROWS)-1:0]     rd_row,
    input  wire [$clog2(COLS)-1:0]     rd_col,
    output wire [TRIT_WIDTH-1:0]       rd_data
);

    /* ── Crossbar storage ── */
    reg [TRIT_WIDTH-1:0] cell [0:ROWS-1][0:COLS-1];

    /* ── Write logic ── */
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            integer r, c;
            for (r = 0; r < ROWS; r = r + 1)
                for (c = 0; c < COLS; c = c + 1)
                    cell[r][c] <= 2'b00; /* Unknown */
        end else if (wr_en) begin
            cell[wr_row][wr_col] <= wr_data;
        end
    end

    /* ── Read logic ── */
    assign rd_data = cell[rd_row][rd_col];

    /* ── Trit decode function (2-bit → signed value) ── */
    function signed [1:0] trit_decode;
        input [1:0] encoded;
        begin
            case (encoded)
                2'b10:   trit_decode = -1;
                2'b00:   trit_decode = 0;
                2'b01:   trit_decode = 1;
                default: trit_decode = 0; /* fault → 0 */
            endcase
        end
    endfunction

    /* ── MAC computation (combinational for now) ── */
    integer ri, ci;
    reg signed [7:0] col_sum [0:COLS-1];
    reg mac_computing;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mac_done <= 1'b0;
            mac_computing <= 1'b0;
            mac_result <= {COLS*8{1'b0}};
        end else if (mac_start && !mac_computing) begin
            mac_computing <= 1'b1;
            mac_done <= 1'b0;
            /* Compute all column MACs in parallel */
            for (ci = 0; ci < COLS; ci = ci + 1) begin
                col_sum[ci] = 0;
                for (ri = 0; ri < ROWS; ri = ri + 1) begin
                    col_sum[ci] = col_sum[ci] +
                        trit_decode(input_vector[ri*TRIT_WIDTH +: TRIT_WIDTH]) *
                        trit_decode(cell[ri][ci]);
                end
                mac_result[ci*8 +: 8] <= col_sum[ci];
            end
        end else if (mac_computing) begin
            mac_done <= 1'b1;
            mac_computing <= 1'b0;
        end else begin
            mac_done <= 1'b0;
        end
    end

endmodule
