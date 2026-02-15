/*
 * samsung_cn105745888a_correlator.v
 * Verilog model: Ternary Sequence Correlator — Samsung CN105745888A
 *
 * Implements the hardware correlator for cyclic-shift demodulation
 * as described in patent CN105745888A:
 *
 *   1. Parallel correlator bank — computes Corr_g for all g ∈ Z_N
 *      simultaneously (patent Eq. 6 for coherent, Eq. 7 for non-coh).
 *
 *   2. Argmax unit — identifies g_est = argmax(Corr_g) in O(log N).
 *
 *   3. Cyclic shift generator — precomputes L^g{tb} for all g.
 *
 *   4. Absolute-value projector — computes |base| for non-coherent mode.
 *
 * Key:
 *   - Ternary elements encoded as 2-bit signed: 10=-1, 00=0, 01=+1
 *   - N correlators run in parallel for single-cycle demodulation
 *   - Configurable for lengths 8, 16, or 32 (OOK families)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ===================================================================== */
/* Ternary multiply-accumulate: a · b for 2-bit ternary                  */
/* ===================================================================== */
module samsung_tseq_mac (
    input  wire [1:0] a,     /* 2-bit ternary: 10=-1, 00=0, 01=+1 */
    input  wire [1:0] b,     /* 2-bit ternary: 10=-1, 00=0, 01=+1 */
    output wire [1:0] prod   /* 2-bit ternary product               */
);

    /* Product truth table (ternary multiply):
     *   (-1)·(-1)= +1,  (-1)·0= 0,  (-1)·(+1)= -1
     *   0·(-1)   = 0,   0·0  = 0,   0·(+1)   = 0
     *   (+1)·(-1)= -1,  (+1)·0= 0,  (+1)·(+1)= +1
     */
    wire a_neg = a[1] & ~a[0];  /* a == -1 */
    wire a_pos = ~a[1] & a[0];  /* a == +1 */
    wire b_neg = b[1] & ~b[0];  /* b == -1 */
    wire b_pos = ~b[1] & b[0];  /* b == +1 */

    wire prod_pos = (a_neg & b_neg) | (a_pos & b_pos);
    wire prod_neg = (a_neg & b_pos) | (a_pos & b_neg);

    assign prod = {prod_neg, prod_pos};  /* 10=-1, 01=+1, 00=0 */

endmodule


/* ===================================================================== */
/* Absolute-value projector: |t| for 2-bit ternary → binary              */
/* ===================================================================== */
module samsung_tseq_abs (
    input  wire [1:0] t,     /* 2-bit ternary */
    output wire [1:0] abs_t  /* |t|: 00=0, 01=1 */
);

    /* |0|=0, |+1|=1, |-1|=1 */
    wire is_nonzero = t[0] | t[1];
    assign abs_t = {1'b0, is_nonzero};

endmodule


/* ===================================================================== */
/* Single correlator: Corr_g = Σ rx[i] · ref[i]                         */
/* Computes correlation of received sequence with one reference shift.   */
/* ===================================================================== */
module samsung_tseq_single_correlator #(
    parameter N = 8       /* Sequence length */
) (
    input  wire              clk,
    input  wire              rst_n,
    input  wire              start,
    input  wire [2*N-1:0]    rx_seq,    /* Received: N×2-bit ternary */
    input  wire [2*N-1:0]    ref_seq,   /* Reference: N×2-bit ternary */
    output reg  signed [15:0] corr_out, /* Correlation value */
    output reg               done
);

    integer i;
    reg signed [15:0] accumulator;
    wire [1:0] products [0:N-1];

    /* Instantiate MAC units for all positions */
    genvar gi;
    generate
        for (gi = 0; gi < N; gi = gi + 1) begin : mac_gen
            samsung_tseq_mac mac_inst (
                .a(rx_seq[2*gi+1 : 2*gi]),
                .b(ref_seq[2*gi+1 : 2*gi]),
                .prod(products[gi])
            );
        end
    endgenerate

    /* Pipeline: accumulate on clock edge */
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            corr_out <= 16'sd0;
            done <= 1'b0;
        end else if (start) begin
            accumulator = 16'sd0;
            for (i = 0; i < N; i = i + 1) begin
                case (products[i])
                    2'b01:   accumulator = accumulator + 16'sd1;
                    2'b10:   accumulator = accumulator - 16'sd1;
                    default: accumulator = accumulator;
                endcase
            end
            corr_out <= accumulator;
            done <= 1'b1;
        end else begin
            done <= 1'b0;
        end
    end

endmodule


/* ===================================================================== */
/* Cyclic shift generator: produces all N shifts of base sequence.       */
/* ===================================================================== */
module samsung_tseq_shift_gen #(
    parameter N = 8
) (
    input  wire [2*N-1:0]    base_seq, /* Base sequence (N×2-bit) */
    input  wire [$clog2(N)-1:0] shift, /* Shift amount g */
    output wire [2*N-1:0]    shifted   /* L^g{base} */
);

    /* Barrel shifter: rotate left by g elements (2 bits each) */
    wire [4*N-1:0] doubled = {base_seq, base_seq};
    wire [$clog2(N)+1-1:0] bit_shift = {shift, 1'b0};  /* ×2 for 2-bit elements */

    assign shifted = doubled[bit_shift +: 2*N];

endmodule


/* ===================================================================== */
/* Argmax unit: find shift with maximum correlation.                     */
/* ===================================================================== */
module samsung_tseq_argmax #(
    parameter N = 8
) (
    input  wire              clk,
    input  wire              rst_n,
    input  wire              start,
    input  wire signed [16*N-1:0] corr_values, /* N×16-bit correlations */
    output reg  [$clog2(N)-1:0]   best_shift,
    output reg  signed [15:0]     max_corr,
    output reg                    done
);

    integer i;
    reg signed [15:0] current_max;
    reg [$clog2(N)-1:0] current_idx;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            best_shift <= 0;
            max_corr   <= 16'sd0;
            done       <= 1'b0;
        end else if (start) begin
            current_max = corr_values[15:0];
            current_idx = 0;
            for (i = 1; i < N; i = i + 1) begin
                if ($signed(corr_values[16*i +: 16]) > current_max) begin
                    current_max = corr_values[16*i +: 16];
                    current_idx = i[$clog2(N)-1:0];
                end
            end
            best_shift <= current_idx;
            max_corr   <= current_max;
            done       <= 1'b1;
        end else begin
            done <= 1'b0;
        end
    end

endmodule


/* ===================================================================== */
/* Top-level: N-way parallel correlator bank + argmax                    */
/* Patent Fig. 10 receiver: correlate all shifts, pick maximum.          */
/* ===================================================================== */
module samsung_tseq_demodulator #(
    parameter N = 8
) (
    input  wire              clk,
    input  wire              rst_n,
    input  wire              start,
    input  wire              coherent,     /* 1=coherent, 0=non-coherent */
    input  wire [2*N-1:0]    base_seq,     /* Base ternary sequence */
    input  wire [2*N-1:0]    rx_seq,       /* Received sequence */
    output wire [$clog2(N)-1:0] symbol_out, /* Detected symbol shift */
    output wire signed [15:0]   max_corr,   /* Maximum correlation */
    output wire                 done
);

    /* --- Reference generation --- */
    wire [2*N-1:0] abs_base;          /* |base| for non-coherent */
    wire [2*N-1:0] ref_in;            /* Selected reference input */

    /* Compute |base_seq| element-wise */
    genvar ai;
    generate
        for (ai = 0; ai < N; ai = ai + 1) begin : abs_gen
            samsung_tseq_abs abs_inst (
                .t(base_seq[2*ai+1 : 2*ai]),
                .abs_t(abs_base[2*ai+1 : 2*ai])
            );
        end
    endgenerate

    /* Mux: coherent uses base, non-coherent uses |base| */
    assign ref_in = coherent ? base_seq : abs_base;

    /* --- Prepare effective RX: non-coherent uses |rx| too --- */
    wire [2*N-1:0] abs_rx;
    generate
        for (ai = 0; ai < N; ai = ai + 1) begin : abs_rx_gen
            samsung_tseq_abs abs_rx_inst (
                .t(rx_seq[2*ai+1 : 2*ai]),
                .abs_t(abs_rx[2*ai+1 : 2*ai])
            );
        end
    endgenerate

    wire [2*N-1:0] effective_rx = coherent ? rx_seq : abs_rx;

    /* --- N parallel correlators --- */
    wire signed [15:0] corr_bank [0:N-1];
    wire [N-1:0] corr_done;

    genvar gi;
    generate
        for (gi = 0; gi < N; gi = gi + 1) begin : corr_gen
            wire [2*N-1:0] shifted_ref;

            samsung_tseq_shift_gen #(.N(N)) shift_inst (
                .base_seq(ref_in),
                .shift(gi[$clog2(N)-1:0]),
                .shifted(shifted_ref)
            );

            samsung_tseq_single_correlator #(.N(N)) corr_inst (
                .clk(clk),
                .rst_n(rst_n),
                .start(start),
                .rx_seq(effective_rx),
                .ref_seq(shifted_ref),
                .corr_out(corr_bank[gi]),
                .done(corr_done[gi])
            );
        end
    endgenerate

    /* Pack correlation values for argmax */
    wire signed [16*N-1:0] packed_corr;
    generate
        for (gi = 0; gi < N; gi = gi + 1) begin : pack_gen
            assign packed_corr[16*gi +: 16] = corr_bank[gi];
        end
    endgenerate

    /* All correlators done? */
    wire all_done = &corr_done;

    /* --- Argmax --- */
    samsung_tseq_argmax #(.N(N)) argmax_inst (
        .clk(clk),
        .rst_n(rst_n),
        .start(all_done),
        .corr_values(packed_corr),
        .best_shift(symbol_out),
        .max_corr(max_corr),
        .done(done)
    );

endmodule
