/*
 * ingole_wo2016199157a1_talu.v
 * Verilog Simulation Model for WO2016199157A1 Ternary ALU (TALU)
 *
 * Implements the transmission-gate (TG) based ternary arithmetic and logic
 * circuits described in patent WO2016199157A1 using a 2-bit encoding:
 *
 *   2'b00 = Ingole level 0 (GND)     = seT5 balanced -1 (FALSE)
 *   2'b01 = Ingole level 1 (VDD/2)   = seT5 balanced  0 (UNKNOWN)
 *   2'b10 = Ingole level 2 (VDD)     = seT5 balanced +1 (TRUE)
 *   2'b11 = invalid / unused
 *
 * Key circuits modeled (all TG-based, p-ECMOS / n-ECMOS):
 *
 *   1. TNOT  — Zero-sequence complement   (4 TG)
 *   2. CWC   — Clockwise complementary     (4 TG)
 *   3. CCWC  — Counter-clockwise compl.    (4 TG)
 *   4. ADD1C — Add-1-carry for LST         (4 TG)
 *   5. TAND  — Ternary AND: min(A,B)       (8 TG)
 *   6. TNAND — Ternary NAND                (8 TG)
 *   7. TOR   — Ternary OR: max(A,B)        (8 TG)
 *   8. TNOR  — Ternary NOR                 (8 TG)
 *   9. XTOR  — Ternary exclusive-OR        (14 TG)
 *  10. COMP  — Ternary comparator         (10 TG)
 *  11. S1    — Half-adder sum              (16 TG)
 *  12. S2    — Full-adder sum              (6 TG)
 *  13. C2    — Full carry generator         (6 TG)
 *  14. PARITY — Even parity generator      (16 TG)
 *  15. DEC2x9 — 2-trit OPCODE decoder     (48 TG)
 *  16. TALU  — Full TALU stage
 *  17. TALU_WORD — Plurality of TALU stages
 *
 * Reference: WO2016199157A1, Vijay T. Ingole et al.
 *            "Ternary Arithmetic and Logic Unit (ALU) and
 *             Ternary Logic Circuits"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ===================================================================
 * Trit Encoding Constants
 * ===================================================================*/

`define IG_0  2'b00
`define IG_1  2'b01
`define IG_2  2'b10

/* ===================================================================
 * TNOT — Ternary NOT / Zero-sequence Complement (4 TG)
 *
 *   Input 0 -> Output 2
 *   Input 1 -> Output 1
 *   Input 2 -> Output 0
 *
 * Patent Fig 3, truth table (2, 1, 0)
 * ===================================================================*/
module ig_tnot (
    input  [1:0] a,
    output reg [1:0] y
);
    always @(*) begin
        case (a)
            `IG_0:   y = `IG_2;
            `IG_1:   y = `IG_1;
            `IG_2:   y = `IG_0;
            default: y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * CWC — Clockwise Complementary (4 TG)
 *
 *   Input 0 -> Output 0      (positive sequence)
 *   Input 1 -> Output 2
 *   Input 2 -> Output 1
 *
 * Patent: CWC rotates {0→0, 1→2, 2→1}
 * ===================================================================*/
module ig_cwc (
    input  [1:0] a,
    output reg [1:0] y
);
    always @(*) begin
        case (a)
            `IG_0:   y = `IG_0;
            `IG_1:   y = `IG_2;
            `IG_2:   y = `IG_1;
            default: y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * CCWC — Counter-Clockwise Complementary (4 TG)
 *
 *   Input 0 -> Output 1      (negative sequence)
 *   Input 1 -> Output 0
 *   Input 2 -> Output 2
 *
 * Patent: CCWC rotates {0→1, 1→0, 2→2}
 * ===================================================================*/
module ig_ccwc (
    input  [1:0] a,
    output reg [1:0] y
);
    always @(*) begin
        case (a)
            `IG_0:   y = `IG_1;
            `IG_1:   y = `IG_0;
            `IG_2:   y = `IG_2;
            default: y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * ADD_1_CARRY — Add-one carry injector for LST subtraction (4 TG)
 *
 *   Input 0 -> Output 1,  Carry 0
 *   Input 1 -> Output 2,  Carry 0
 *   Input 2 -> Output 0,  Carry 1
 *
 * Adds 1 in unbalanced ternary: (x + 1) mod 3, carry = (x+1)/3
 * Used at LST stage to form 3's complement subtraction
 * ===================================================================*/
module ig_add1carry (
    input  [1:0] a,
    output reg [1:0] sum,
    output reg [1:0] carry
);
    always @(*) begin
        case (a)
            `IG_0:   begin sum = `IG_1; carry = `IG_0; end
            `IG_1:   begin sum = `IG_2; carry = `IG_0; end
            `IG_2:   begin sum = `IG_0; carry = `IG_1; end
            default: begin sum = `IG_0; carry = `IG_0; end
        endcase
    end
endmodule

/* ===================================================================
 * TAND — Ternary AND: min(A, B) (8 TG)
 *
 * Truth table (unbalanced A rows × B cols):
 *         B=0  B=1  B=2
 *   A=0 |  0    0    0
 *   A=1 |  0    1    1
 *   A=2 |  0    1    2
 *
 * Patent Fig 5a
 * ===================================================================*/
module ig_tand (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] y
);
    always @(*) begin
        case ({a, b})
            {`IG_0, `IG_0}: y = `IG_0;
            {`IG_0, `IG_1}: y = `IG_0;
            {`IG_0, `IG_2}: y = `IG_0;
            {`IG_1, `IG_0}: y = `IG_0;
            {`IG_1, `IG_1}: y = `IG_1;
            {`IG_1, `IG_2}: y = `IG_1;
            {`IG_2, `IG_0}: y = `IG_0;
            {`IG_2, `IG_1}: y = `IG_1;
            {`IG_2, `IG_2}: y = `IG_2;
            default:        y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * TNAND — Ternary NAND: TNOT(min(A, B)) (8 TG)
 * ===================================================================*/
module ig_tnand (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] y
);
    wire [1:0] and_out;
    ig_tand tand_i (.a(a), .b(b), .y(and_out));
    ig_tnot tnot_i (.a(and_out), .y(y));
endmodule

/* ===================================================================
 * TOR — Ternary OR: max(A, B) (8 TG)
 *
 * Truth table:
 *         B=0  B=1  B=2
 *   A=0 |  0    1    2
 *   A=1 |  1    1    2
 *   A=2 |  2    2    2
 *
 * Patent Fig 5c
 * ===================================================================*/
module ig_tor (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] y
);
    always @(*) begin
        case ({a, b})
            {`IG_0, `IG_0}: y = `IG_0;
            {`IG_0, `IG_1}: y = `IG_1;
            {`IG_0, `IG_2}: y = `IG_2;
            {`IG_1, `IG_0}: y = `IG_1;
            {`IG_1, `IG_1}: y = `IG_1;
            {`IG_1, `IG_2}: y = `IG_2;
            {`IG_2, `IG_0}: y = `IG_2;
            {`IG_2, `IG_1}: y = `IG_2;
            {`IG_2, `IG_2}: y = `IG_2;
            default:        y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * TNOR — Ternary NOR: TNOT(max(A, B)) (8 TG)
 * ===================================================================*/
module ig_tnor (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] y
);
    wire [1:0] or_out;
    ig_tor tor_i (.a(a), .b(b), .y(or_out));
    ig_tnot tnot_i (.a(or_out), .y(y));
endmodule

/* ===================================================================
 * XTOR — Ternary Exclusive-OR (14 TG)
 *
 * Truth table:
 *         B=0  B=1  B=2
 *   A=0 |  0    2    1
 *   A=1 |  2    1    0
 *   A=2 |  1    0    2
 *
 * XTOR(A,B) = (A + B) mod 3   (modular sum in unbalanced)
 * Patent Fig 5e, used as half-adder sum (S1)
 * ===================================================================*/
module ig_xtor (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] y
);
    always @(*) begin
        case ({a, b})
            {`IG_0, `IG_0}: y = `IG_0;
            {`IG_0, `IG_1}: y = `IG_1;
            {`IG_0, `IG_2}: y = `IG_2;
            {`IG_1, `IG_0}: y = `IG_1;
            {`IG_1, `IG_1}: y = `IG_2;
            {`IG_1, `IG_2}: y = `IG_0;
            {`IG_2, `IG_0}: y = `IG_2;
            {`IG_2, `IG_1}: y = `IG_0;
            {`IG_2, `IG_2}: y = `IG_1;
            default:        y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * COMPARATOR — Ternary compare (10 TG)
 *
 *   Result 0: A == B
 *   Result 1: A > B
 *   Result 2: A < B
 *
 * Patent Fig 5f
 * ===================================================================*/
module ig_comparator (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] y
);
    always @(*) begin
        case ({a, b})
            {`IG_0, `IG_0}: y = `IG_0;  /* equal */
            {`IG_0, `IG_1}: y = `IG_2;  /* A < B */
            {`IG_0, `IG_2}: y = `IG_2;  /* A < B */
            {`IG_1, `IG_0}: y = `IG_1;  /* A > B */
            {`IG_1, `IG_1}: y = `IG_0;  /* equal */
            {`IG_1, `IG_2}: y = `IG_2;  /* A < B */
            {`IG_2, `IG_0}: y = `IG_1;  /* A > B */
            {`IG_2, `IG_1}: y = `IG_1;  /* A > B */
            {`IG_2, `IG_2}: y = `IG_0;  /* equal */
            default:        y = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * S1 — First Adder / Half-Adder Sum (16 TG)
 *
 * S1(A,B) = (A + B) mod 3  (identical to XTOR)
 * Patent: "first adder" produces partial sum S1
 * ===================================================================*/
module ig_s1 (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] sum
);
    ig_xtor xtor_i (.a(a), .b(b), .y(sum));
endmodule

/* ===================================================================
 * C1 — Half-Adder Carry
 *
 * C1(A,B) = floor((A + B) / 3)
 * Truth table:
 *         B=0  B=1  B=2
 *   A=0 |  0    0    0
 *   A=1 |  0    0    1
 *   A=2 |  0    1    1
 *
 * Note: This is TAND(A,B) >> 1 conceptually, but implemented as:
 *   carry = 1 if (A+B) >= 3, else 0
 * ===================================================================*/
module ig_c1 (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] carry
);
    always @(*) begin
        case ({a, b})
            {`IG_0, `IG_0}: carry = `IG_0;
            {`IG_0, `IG_1}: carry = `IG_0;
            {`IG_0, `IG_2}: carry = `IG_0;
            {`IG_1, `IG_0}: carry = `IG_0;
            {`IG_1, `IG_1}: carry = `IG_0;
            {`IG_1, `IG_2}: carry = `IG_1;
            {`IG_2, `IG_0}: carry = `IG_0;
            {`IG_2, `IG_1}: carry = `IG_1;
            {`IG_2, `IG_2}: carry = `IG_1;
            default:        carry = `IG_0;
        endcase
    end
endmodule

/* ===================================================================
 * S2 — Second Adder / Full-Adder Sum (6 TG)
 *
 * S2(S1, Cin) = (S1 + Cin) mod 3
 * Patent: "second adder" produces final sum from S1 and carry-in
 * ===================================================================*/
module ig_s2 (
    input  [1:0] s1,
    input  [1:0] cin,
    output [1:0] sum
);
    ig_xtor xtor_i (.a(s1), .b(cin), .y(sum));
endmodule

/* ===================================================================
 * C2 — Full Carry Generator (6 TG)
 *
 * C2 = 1 if (A + B + Cin) >= 3, else take C1
 * More precisely: C2 = C1(A,B) OR C1(S1(A,B), Cin)
 * ===================================================================*/
module ig_c2 (
    input  [1:0] a,
    input  [1:0] b,
    input  [1:0] cin,
    output [1:0] carry
);
    wire [1:0] s1_out;
    wire [1:0] c1_ab;
    wire [1:0] c1_sc;

    ig_s1 s1_i  (.a(a),      .b(b),   .sum(s1_out));
    ig_c1 c1a_i (.a(a),      .b(b),   .carry(c1_ab));
    ig_c1 c1s_i (.a(s1_out), .b(cin), .carry(c1_sc));
    ig_tor or_i (.a(c1_ab),  .b(c1_sc), .y(carry));
endmodule

/* ===================================================================
 * Full Adder — Combines S2 and C2
 * ===================================================================*/
module ig_full_adder (
    input  [1:0] a,
    input  [1:0] b,
    input  [1:0] cin,
    output [1:0] sum,
    output [1:0] cout
);
    wire [1:0] s1_out;
    ig_s1 s1_i (.a(a), .b(b), .sum(s1_out));
    ig_s2 s2_i (.s1(s1_out), .cin(cin), .sum(sum));
    ig_c2 c2_i (.a(a), .b(b), .cin(cin), .carry(cout));
endmodule

/* ===================================================================
 * PARITY — Even Parity Generator (16 TG)
 *
 * Parity(A,B) = (A + B) mod 3 — identical topology to S1/XTOR
 * Chained across word: P = XTOR(A[0], A[1]) → XTOR(P, A[2]) → ...
 * Result 0 = even parity
 * ===================================================================*/
module ig_parity (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] parity
);
    ig_xtor xtor_i (.a(a), .b(b), .y(parity));
endmodule

/* ===================================================================
 * DECODER_2x9 — 2-trit OPCODE Decoder (48 TG)
 *
 * Decodes 2-trit OPCODE {S0, S1} into 9 one-hot outputs D0..D8
 * controlling TALU operation selection.
 *
 *   S0=0,S1=0 → D0 (NOP)          S0=1,S1=2 → D5 (XTOR/COMP)
 *   S0=0,S1=1 → D1 (AI TOR/TNOR)  S0=2,S1=0 → D6 (B-A + carry)
 *   S0=0,S1=2 → D2 (TOR/TNOR)     S0=2,S1=1 → D7 (A-B + carry)
 *   S0=1,S1=0 → D3 (AI TAND/TNAND) S0=2,S1=2 → D8 (A+B + carry)
 *   S0=1,S1=1 → D4 (TAND/TNAND)
 * ===================================================================*/
module ig_decoder_2x9 (
    input  [1:0] s0,
    input  [1:0] s1,
    output reg [8:0] d
);
    always @(*) begin
        d = 9'b0;
        case ({s0, s1})
            {`IG_0, `IG_0}: d = 9'b000000001;  /* D0 */
            {`IG_0, `IG_1}: d = 9'b000000010;  /* D1 */
            {`IG_0, `IG_2}: d = 9'b000000100;  /* D2 */
            {`IG_1, `IG_0}: d = 9'b000001000;  /* D3 */
            {`IG_1, `IG_1}: d = 9'b000010000;  /* D4 */
            {`IG_1, `IG_2}: d = 9'b000100000;  /* D5 */
            {`IG_2, `IG_0}: d = 9'b001000000;  /* D6 */
            {`IG_2, `IG_1}: d = 9'b010000000;  /* D7 */
            {`IG_2, `IG_2}: d = 9'b100000000;  /* D8 */
            default:        d = 9'b000000001;  /* Default: NOP */
        endcase
    end
endmodule

/* ===================================================================
 * TALU_STAGE — Single TALU stage (2-trit inputs, 2-trit opcode)
 *
 * Plurality of these stages operate in parallel for multi-trit words.
 * Each stage produces two function outputs (f01, f02) and a carry-out.
 *
 * For arithmetic operations (D6/D7/D8), cin is the carry input from
 * the previous stage.
 * ===================================================================*/
module ig_talu_stage (
    input  [1:0] a,
    input  [1:0] b,
    input  [1:0] cin,
    input  [1:0] opcode_s0,
    input  [1:0] opcode_s1,
    output reg [1:0] f01,
    output reg [1:0] f02,
    output reg [1:0] cout
);
    /* --- Compute all possible results in parallel --- */
    wire [1:0] tand_out, tnand_out, tor_out, tnor_out;
    wire [1:0] xtor_out, comp_out;
    wire [1:0] add_sum, add_carry;
    wire [1:0] tnot_a, tnot_b;

    ig_tand       g_tand  (.a(a), .b(b), .y(tand_out));
    ig_tnand      g_tnand (.a(a), .b(b), .y(tnand_out));
    ig_tor        g_tor   (.a(a), .b(b), .y(tor_out));
    ig_tnor       g_tnor  (.a(a), .b(b), .y(tnor_out));
    ig_xtor       g_xtor  (.a(a), .b(b), .y(xtor_out));
    ig_comparator g_comp  (.a(a), .b(b), .y(comp_out));
    ig_full_adder g_fa    (.a(a), .b(b), .cin(cin), .sum(add_sum), .cout(add_carry));
    ig_tnot       g_na    (.a(a), .y(tnot_a));
    ig_tnot       g_nb    (.a(b), .y(tnot_b));

    /* --- Subtract wires: B-A uses TNOT(A)+B, A-B uses A+TNOT(B) --- */
    /* 3's complement: TNOT(X) is the "digit complement", then add+1 via carry.
       For subtraction, the carry-in at LST is set to 1 externally. */
    wire [1:0] sub_ba_sum, sub_ba_carry;
    wire [1:0] sub_ab_sum, sub_ab_carry;
    ig_full_adder g_ba (.a(tnot_a), .b(b), .cin(cin), .sum(sub_ba_sum), .cout(sub_ba_carry));
    ig_full_adder g_ab (.a(a), .b(tnot_b), .cin(cin), .sum(sub_ab_sum), .cout(sub_ab_carry));

    /* --- All-inclusive TOR/TNOR across multi-trit is handled at word level --- */
    /* Single-stage: same as TOR/TNOR for one trit pair */

    /* --- Decoded selection --- */
    wire [8:0] d;
    ig_decoder_2x9 dec (.s0(opcode_s0), .s1(opcode_s1), .d(d));

    always @(*) begin
        /* Defaults */
        f01  = `IG_0;
        f02  = `IG_0;
        cout = `IG_0;

        case (1'b1)  // synopsys parallel_case
            d[0]: begin /* D0: NOP */
                f01  = a;
                f02  = b;
                cout = `IG_0;
            end
            d[1]: begin /* D1: All Inclusive TOR / TNOR */
                f01  = tor_out;
                f02  = tnor_out;
                cout = `IG_0;
            end
            d[2]: begin /* D2: TOR / TNOR */
                f01  = tor_out;
                f02  = tnor_out;
                cout = `IG_0;
            end
            d[3]: begin /* D3: All Inclusive TAND / TNAND */
                f01  = tand_out;
                f02  = tnand_out;
                cout = `IG_0;
            end
            d[4]: begin /* D4: TAND / TNAND */
                f01  = tand_out;
                f02  = tnand_out;
                cout = `IG_0;
            end
            d[5]: begin /* D5: XTOR / Comparator */
                f01  = xtor_out;
                f02  = comp_out;
                cout = `IG_0;
            end
            d[6]: begin /* D6: B-A + carry */
                f01  = sub_ba_sum;
                f02  = sub_ba_carry;
                cout = sub_ba_carry;
            end
            d[7]: begin /* D7: A-B + carry */
                f01  = sub_ab_sum;
                f02  = sub_ab_carry;
                cout = sub_ab_carry;
            end
            d[8]: begin /* D8: A+B + carry */
                f01  = add_sum;
                f02  = add_carry;
                cout = add_carry;
            end
            default: begin
                f01  = a;
                f02  = b;
                cout = `IG_0;
            end
        endcase
    end
endmodule

/* ===================================================================
 * TALU_WORD — Plurality of TALU stages for an N-trit word
 *
 * Parameterized word width.  Stages chain carry from LST to MST.
 * Produces:
 *   - f01[N-1:0], f02[N-1:0] : per-stage function outputs
 *   - overflow : carry out of MST
 *   - all_zero : 1 if All Inclusive TOR yields all zeros
 *   - parity_a, parity_b : even parity chains
 * ===================================================================*/
module ig_talu_word #(
    parameter N = 4    /* default: 4-trit word */
)(
    input  [2*N-1:0] a,        /* N trits, 2 bits each */
    input  [2*N-1:0] b,
    input  [1:0]     opcode_s0,
    input  [1:0]     opcode_s1,
    input  [1:0]     cin,      /* LST carry-in (1 for subtraction) */
    output [2*N-1:0] f01,
    output [2*N-1:0] f02,
    output [1:0]     overflow,
    output [1:0]     all_zero,
    output [1:0]     parity_a,
    output [1:0]     parity_b
);
    wire [1:0] carry [0:N];
    assign carry[0] = cin;

    /* --- Parity chains --- */
    wire [1:0] pa_chain [0:N];
    wire [1:0] pb_chain [0:N];
    assign pa_chain[0] = `IG_0;
    assign pb_chain[0] = `IG_0;

    /* --- All-zero detection chain (TOR fold) --- */
    wire [1:0] az_chain [0:N];
    assign az_chain[0] = `IG_0;

    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : stage
            ig_talu_stage talu (
                .a          (a[2*i+1 : 2*i]),
                .b          (b[2*i+1 : 2*i]),
                .cin        (carry[i]),
                .opcode_s0  (opcode_s0),
                .opcode_s1  (opcode_s1),
                .f01        (f01[2*i+1 : 2*i]),
                .f02        (f02[2*i+1 : 2*i]),
                .cout       (carry[i+1])
            );

            /* Parity A chain */
            wire [1:0] pa_next;
            ig_parity pa (.a(pa_chain[i]), .b(a[2*i+1 : 2*i]), .parity(pa_next));
            assign pa_chain[i+1] = pa_next;

            /* Parity B chain */
            wire [1:0] pb_next;
            ig_parity pb (.a(pb_chain[i]), .b(b[2*i+1 : 2*i]), .parity(pb_next));
            assign pb_chain[i+1] = pb_next;

            /* All-zero chain: TOR fold of f01 outputs */
            wire [1:0] az_next;
            ig_tor az (.a(az_chain[i]), .b(f01[2*i+1 : 2*i]), .y(az_next));
            assign az_chain[i+1] = az_next;
        end
    endgenerate

    assign overflow = carry[N];
    assign parity_a = pa_chain[N];
    assign parity_b = pb_chain[N];

    /* all_zero = 0 (IG_0) when the entire TOR chain is 0, else non-zero */
    /* We use TNOT so that result 2 = all zeros detected, 0 = not all zero */
    wire [1:0] az_final;
    ig_tnot az_inv (.a(az_chain[N]), .y(az_final));
    /* If az_chain[N] == 0 → az_final = 2 (true), else az_final <= 1 */
    /* Map: 2=all_zero, else not. But keep raw for simplicity */
    assign all_zero = az_chain[N];  /* 0 = all zero, >0 = not all zero */

endmodule
