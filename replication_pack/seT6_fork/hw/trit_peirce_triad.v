/**
 * trit_peirce_triad.v – Peircean Triadic Sign Classifier (Synthesisable RTL)
 *
 * Hardware implementation of Peirce's sign classification system.
 * Takes three 2-bit trit inputs (trichotomies I, II, III) and outputs:
 *   - valid:    whether the combination is one of the 10 Peircean classes
 *   - class_id: the class number (1–10, encoded in 4 bits)
 *   - category: the dominant phenomenological category
 *
 * Trit encoding (same as trit_art9_pipeline.v):
 *   2'b00 = -1 (Firstness)
 *   2'b01 =  0 (Secondness)
 *   2'b10 = +1 (Thirdness)
 *   2'b11 = fault
 *
 * The constraint for valid classes is: I >= II >= III
 * (Firstness=-1 < Secondness=0 < Thirdness=+1)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

module ternary_peirce_classifier (
    input  wire [1:0] trich_i,     // Trichotomy I:   sign itself
    input  wire [1:0] trich_ii,    // Trichotomy II:  sign→object
    input  wire [1:0] trich_iii,   // Trichotomy III: sign→interpretant
    output reg        valid,       // 1 if valid Peircean class
    output reg  [3:0] class_id,    // Class I–X (1–10), 0 if invalid
    output reg  [1:0] category     // Dominant category of the sign
);

    /* Convert 2-bit encoding to signed comparison values:
       00 → 0 (maps to -1), 01 → 1 (maps to 0), 10 → 2 (maps to +1) */
    wire [1:0] t1 = trich_i;
    wire [1:0] t2 = trich_ii;
    wire [1:0] t3 = trich_iii;

    /* Fault detection */
    wire fault = (t1 == 2'b11) | (t2 == 2'b11) | (t3 == 2'b11);

    /* Validity: t1 >= t2 >= t3 (in the 2-bit unsigned encoding,
       the ordering 00 < 01 < 10 matches Firstness < Secondness < Thirdness) */
    wire ge_12 = (t1 >= t2);
    wire ge_23 = (t2 >= t3);

    always @(*) begin
        if (fault) begin
            valid    = 1'b0;
            class_id = 4'd0;
            category = 2'b11;
        end else if (ge_12 && ge_23) begin
            valid = 1'b1;
            /* Map (t1,t2,t3) to class ID via lookup.
               Encoding: 00=-1, 01=0, 10=+1 → compose 6-bit key */
            case ({t1, t2, t3})
                6'b00_00_00: class_id = 4'd1;   /* I:   (-1,-1,-1) */
                6'b01_00_00: class_id = 4'd2;   /* II:  ( 0,-1,-1) */
                6'b01_01_00: class_id = 4'd3;   /* III: ( 0, 0,-1) */
                6'b01_01_01: class_id = 4'd4;   /* IV:  ( 0, 0, 0) */
                6'b10_00_00: class_id = 4'd5;   /* V:   (+1,-1,-1) */
                6'b10_01_00: class_id = 4'd6;   /* VI:  (+1, 0,-1) */
                6'b10_01_01: class_id = 4'd7;   /* VII: (+1, 0, 0) */
                6'b10_10_00: class_id = 4'd8;   /* VIII:(+1,+1,-1) */
                6'b10_10_01: class_id = 4'd9;   /* IX:  (+1,+1, 0) */
                6'b10_10_10: class_id = 4'd10;  /* X:   (+1,+1,+1) */
                default:     class_id = 4'd0;   /* Should not reach */
            endcase
            /* Dominant category = the highest category present (= t1) */
            category = t1;
        end else begin
            valid    = 1'b0;
            class_id = 4'd0;
            category = 2'b11;
        end
    end

endmodule

/**
 * Triadic determination gate.
 *
 * Models Peirce's irreducible triadic relation: Object → Sign → Interpretant.
 * The output is a "mediation" trit computed by ternary majority voting —
 * if all three agree, output is that value; if two agree, output is majority;
 * if all differ, output is Unknown (genuine mediation required).
 */
module ternary_peirce_mediation (
    input  wire [1:0] object,
    input  wire [1:0] sign,
    input  wire [1:0] interpretant,
    output reg  [1:0] mediation,
    output reg        unanimous     // 1 if all three agree
);

    /* Decode to signed: 00→-1, 01→0, 10→+1 */
    wire signed [1:0] o_s = (object == 2'b00) ? -2'sd1 :
                            (object == 2'b10) ?  2'sd1 : 2'sd0;
    wire signed [1:0] s_s = (sign == 2'b00) ? -2'sd1 :
                            (sign == 2'b10) ?  2'sd1 : 2'sd0;
    wire signed [1:0] i_s = (interpretant == 2'b00) ? -2'sd1 :
                            (interpretant == 2'b10) ?  2'sd1 : 2'sd0;

    wire signed [2:0] sum = o_s + s_s + i_s;

    always @(*) begin
        unanimous = (object == sign) && (sign == interpretant) &&
                    (object != 2'b11);

        if (object == 2'b11 || sign == 2'b11 || interpretant == 2'b11) begin
            mediation = 2'b11;  /* Fault propagation */
        end else if (sum >= 2) begin
            mediation = 2'b10;  /* +1: Thirdness dominant */
        end else if (sum <= -2) begin
            mediation = 2'b00;  /* -1: Firstness dominant */
        end else if (object == sign) begin
            mediation = object;
        end else if (sign == interpretant) begin
            mediation = sign;
        end else if (object == interpretant) begin
            mediation = object;
        end else begin
            mediation = 2'b01;  /* 0: Unknown / genuine mediation */
        end
    end

endmodule

/**
 * Semiosis chain register.
 *
 * On each clock edge, the interpretant output feeds back as the next sign
 * input, modelling Peirce's unlimited semiosis. The chain converges when
 * the mediation stabilises for N consecutive cycles (convergence detector).
 */
module ternary_semiosis_chain #(
    parameter DEPTH = 8
) (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        enable,
    input  wire [1:0]  object_in,
    input  wire [1:0]  sign_in,        // Initial sign (used on reset)
    output reg  [1:0]  current_sign,
    output reg  [1:0]  current_mediation,
    output reg         converged,
    output reg  [3:0]  cycle_count
);

    wire [1:0] med_out;
    wire       unan;

    ternary_peirce_mediation med_gate (
        .object(object_in),
        .sign(current_sign),
        .interpretant(current_sign),  /* Self-interpreting for convergence */
        .mediation(med_out),
        .unanimous(unan)
    );

    reg [1:0] prev_mediation;
    reg [2:0] stable_count;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            current_sign      <= sign_in;
            current_mediation <= 2'b01;
            prev_mediation    <= 2'b01;
            converged         <= 1'b0;
            cycle_count       <= 4'd0;
            stable_count      <= 3'd0;
        end else if (enable && !converged) begin
            current_sign      <= med_out;
            current_mediation <= med_out;
            prev_mediation    <= current_mediation;
            cycle_count       <= cycle_count + 4'd1;

            if (med_out == prev_mediation)
                stable_count <= stable_count + 3'd1;
            else
                stable_count <= 3'd0;

            if (stable_count >= 3'd3)
                converged <= 1'b1;
        end
    end

endmodule
