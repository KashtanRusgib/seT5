/*
 * huawei_cn119652311a_alu.v
 * Verilog Simulation Model for Huawei CN119652311A Ternary ALU
 *
 * Implements the ternary logic gate and computing circuits described in
 * patent CN119652311A using a 2-bit encoding for each trit:
 *
 *   2'b00 = Huawei logic 0 (VGND)    = seT6 balanced -1 (FALSE)
 *   2'b01 = Huawei logic 1 (VDD/2)   = seT6 balanced  0 (UNKNOWN)
 *   2'b10 = Huawei logic 2 (VDD)     = seT6 balanced +1 (TRUE)
 *   2'b11 = invalid / unused
 *
 * Key circuits modeled:
 *
 *   1. NTI  — Negative Ternary Inverter (2 transistors)
 *   2. PTI  — Positive Ternary Inverter (2 transistors)
 *   3. PB   — Positive Buffer           (2 transistors)
 *   4. NB   — Negative Buffer           (2 transistors)
 *   5. INC  — Self-incrementing gate    (7+2 transistors)
 *   6. DEC  — Self-decrementing gate    (7+2 transistors)
 *   7. Tsum — Ternary summing circuit   (Fig 5)
 *   8. THA  — Ternary half-adder       (Fig 6)
 *   9. TFA  — Ternary full-adder       (Fig 7)
 *  10. TMul — Exact 1-trit multiplier
 *  11. ATMul— Approximate 1-trit multiplier
 *  12. Mul2x2 — 2-trit x 2-trit multiplier (Fig 11b)
 *  13. Mul6x6 — 6-trit x 6-trit multiplier (Fig 14)
 *
 * Reference: CN119652311A, Huawei Technologies Co., Ltd.
 *            "Ternary logic gate circuit, computing circuit, chip,
 *             and electronic device"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ===================================================================
 * Trit Encoding Constants
 * ===================================================================*/

/* Huawei unbalanced encoding: 0, 1, 2 */
`define HW_0  2'b00
`define HW_1  2'b01
`define HW_2  2'b10

/* ===================================================================
 * NTI — Negative Ternary Inverter (Patent: f18 = {2,0,0})
 *
 *   Input 0 -> Output 2
 *   Input 1 -> Output 0
 *   Input 2 -> Output 0
 *
 * 2 CNTFET transistors (1 P-type HVT, 1 N-type LVT)
 * ===================================================================*/
module hw_nti (
    input  [1:0] x,
    output reg [1:0] y
);
    always @(*) begin
        case (x)
            `HW_0:   y = `HW_2;
            `HW_1:   y = `HW_0;
            `HW_2:   y = `HW_0;
            default: y = `HW_0;
        endcase
    end
endmodule

/* ===================================================================
 * PTI — Positive Ternary Inverter (Patent: f24 = {2,2,0})
 *
 *   Input 0 -> Output 2
 *   Input 1 -> Output 2
 *   Input 2 -> Output 0
 *
 * 2 CNTFET transistors (1 P-type LVT, 1 N-type HVT)
 * ===================================================================*/
module hw_pti (
    input  [1:0] x,
    output reg [1:0] y
);
    always @(*) begin
        case (x)
            `HW_0:   y = `HW_2;
            `HW_1:   y = `HW_2;
            `HW_2:   y = `HW_0;
            default: y = `HW_0;
        endcase
    end
endmodule

/* ===================================================================
 * PB — Positive Buffer (Patent: f8 = {0,2,2})
 *
 *   Input 0 -> Output 0
 *   Input 1 -> Output 2
 *   Input 2 -> Output 2
 *
 * 2 CNTFET transistors
 * ===================================================================*/
module hw_pb (
    input  [1:0] x,
    output reg [1:0] y
);
    always @(*) begin
        case (x)
            `HW_0:   y = `HW_0;
            `HW_1:   y = `HW_2;
            `HW_2:   y = `HW_2;
            default: y = `HW_0;
        endcase
    end
endmodule

/* ===================================================================
 * NB — Negative Buffer (Patent: f2 = {0,0,2})
 *
 *   Input 0 -> Output 0
 *   Input 1 -> Output 0
 *   Input 2 -> Output 2
 *
 * 2 CNTFET transistors
 * ===================================================================*/
module hw_nb (
    input  [1:0] x,
    output reg [1:0] y
);
    always @(*) begin
        case (x)
            `HW_0:   y = `HW_0;
            `HW_1:   y = `HW_0;
            `HW_2:   y = `HW_2;
            default: y = `HW_0;
        endcase
    end
endmodule

/* ===================================================================
 * INC — Self-Incrementing Gate (Patent: f5 = {1,2,0})
 *
 *   Input 0 -> Output 1   (0+1 mod 3 = 1)
 *   Input 1 -> Output 2   (1+1 mod 3 = 2)
 *   Input 2 -> Output 0   (2+1 mod 3 = 0)
 *
 * Implementation (Patent Claims 1-3):
 *   - NTI preprocessor on input (2 transistors)
 *   - 7 core transistors:
 *       L1 (P-type, LVT): Source=VDD, Drain=output, Gate=NTI(input)
 *       L2 (N-type, LVT): Source=VGND, Drain=output, Gate=NTI(input)
 *       L3 (P-type, LVT): Source=VDD, Drain=node_a, Gate=input
 *       H1 (N-type, HVT): Source=VGND, Drain=node_a, Gate=NTI(input)
 *       H2 (N-type, HVT): Source=node_a, Drain=output, Gate=input
 *       M1 (P-type, MVT): Source=VDD, Drain=output, Gate=input
 *       M2 (N-type, MVT): Source=VGND, Drain=output, Gate=input
 *   Total: 9 transistors (7 core + 2 NTI)
 *
 * Threshold voltages determine which transistors turn on at each
 * input voltage level, yielding the desired truth table.
 * ===================================================================*/
module hw_inc (
    input  [1:0] x,
    output reg [1:0] y
);
    /* Behavioral model of the 9-transistor circuit */
    always @(*) begin
        case (x)
            `HW_0:   y = `HW_1;   /* VGND -> VDD/2 */
            `HW_1:   y = `HW_2;   /* VDD/2 -> VDD  */
            `HW_2:   y = `HW_0;   /* VDD -> VGND   */
            default: y = `HW_0;
        endcase
    end
endmodule

/* ===================================================================
 * DEC — Self-Decrementing Gate (Patent: f19 = {2,0,1})
 *
 *   Input 0 -> Output 2   (0-1 mod 3 = 2)
 *   Input 1 -> Output 0   (1-1 mod 3 = 0)
 *   Input 2 -> Output 1   (2-1 mod 3 = 1)
 *
 * Implementation (Patent Claims 4-6):
 *   - PTI preprocessor on input (2 transistors)
 *   - 7 core transistors with different threshold assignments:
 *       L1 (P-type, LVT): Source=VDD, Drain=output, Gate=PTI(input)
 *       L2 (N-type, LVT): Source=VGND, Drain=output, Gate=PTI(input)
 *       L3 (N-type, LVT): Source=VGND, Drain=node_a, Gate=input
 *       H1 (P-type, HVT): Source=VDD, Drain=node_a, Gate=PTI(input)
 *       H2 (P-type, HVT): Source=node_a, Drain=output, Gate=input
 *       M1 (P-type, MVT): Source=VDD, Drain=output, Gate=input
 *       M2 (N-type, MVT): Source=VGND, Drain=output, Gate=input
 *   Total: 9 transistors (7 core + 2 PTI)
 * ===================================================================*/
module hw_dec (
    input  [1:0] x,
    output reg [1:0] y
);
    always @(*) begin
        case (x)
            `HW_0:   y = `HW_2;   /* VGND -> VDD   */
            `HW_1:   y = `HW_0;   /* VDD/2 -> VGND */
            `HW_2:   y = `HW_1;   /* VDD -> VDD/2  */
            default: y = `HW_0;
        endcase
    end
endmodule

/* ===================================================================
 * Tsum — Ternary Summing Circuit (Patent Fig. 5, Claim 7)
 *
 * Computes S = (A + B) mod 3  (in Huawei's unbalanced encoding)
 *
 * Signal processing module:
 *   1. NTI₁(A)          → signal_n1
 *   2. PTI(A)           → signal_p
 *   3. NTI₂(signal_p)   → signal_n2
 *   4. NOR(signal_n1, signal_n2) → signal_nor
 *
 *   These produce three gating signals:
 *     - signal_n1: logic 2 when A=0, else 0  → selects DEC path
 *     - signal_nor: logic 2 when A=1, else 0 → selects pass-through
 *     - signal_n2: logic 2 when A=2, else 0  → selects INC path
 *
 *   Three gating tubes route B through:
 *     A=0 → DEC(B): sum = B - 1 mod 3  ≡ (0+B) mod 3 ... wait
 *
 *   Actually in Huawei's encoding:
 *     A=0: sum = (0+B) mod 3 = B itself        → pass-through
 *     A=1: sum = (1+B) mod 3 = INC(B)          → INC(B)
 *     A=2: sum = (2+B) mod 3 = INC(INC(B))     → DEC(B) since DEC = +2 mod 3
 *
 *   So signals control:
 *     signal_n1  (A=0) → pass B as-is
 *     signal_nor (A=1) → route B through INC
 *     signal_n2  (A=2) → route B through DEC (= INC+INC = +2)
 * ===================================================================*/
module hw_tsum (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] s
);
    /* Internal signals from preprocessing */
    wire [1:0] nti_a;     /* NTI(A) */
    wire [1:0] pti_a;     /* PTI(A) */
    wire [1:0] nti2_pti;  /* NTI(PTI(A)) */
    wire [1:0] inc_b;     /* INC(B) */
    wire [1:0] dec_b;     /* DEC(B) — equivalent to INC(INC(B)) */

    hw_nti u_nti1   (.x(a),     .y(nti_a));
    hw_pti u_pti    (.x(a),     .y(pti_a));
    hw_nti u_nti2   (.x(pti_a), .y(nti2_pti));
    hw_inc u_inc_b  (.x(b),     .y(inc_b));
    hw_dec u_dec_b  (.x(b),     .y(dec_b));

    /*
     * Gating tube routing:
     *   nti_a    = 2 when A=0, else 0   → gate for pass-through
     *   nti2_pti = 2 when A=2, else 0   → gate for DEC path (+2)
     *   NOR(nti_a, nti2_pti) = 2 when A=1, else 0 → gate for INC path (+1)
     *
     * NOR in ternary: produces 2 only when both inputs are 0
     */
    wire a_is_0 = (nti_a == `HW_2);
    wire a_is_2 = (nti2_pti == `HW_2);
    wire a_is_1 = ~a_is_0 & ~a_is_2;

    always @(*) begin
        if (a_is_0)
            s = b;          /* A=0: sum = 0+B = B */
        else if (a_is_1)
            s = inc_b;      /* A=1: sum = 1+B = INC(B) */
        else
            s = dec_b;      /* A=2: sum = 2+B = DEC(B) */
    end
endmodule

/* ===================================================================
 * Carry Device for Half-Adder (Patent Fig. 6)
 *
 * Carry truth table (Huawei encoding):
 *   A\B | 0 | 1 | 2
 *   ----+---+---+---
 *    0  | 0 | 0 | 0
 *    1  | 0 | 0 | 1
 *    2  | 0 | 1 | 1
 *
 * Carry = 1 when A+B >= 3 (Huawei's carry = floor((A+B)/3))
 *
 * Implemented per patent using PB/NB and AND logic:
 *   carry = PB(A) AND NB(B)   OR   NB(A) AND PB(B)
 *   ... simplified to: carry = 1 when (A+B >= 3)
 * ===================================================================*/
module hw_carry (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] c
);
    wire [1:0] pb_a, nb_a, pb_b, nb_b;

    hw_pb u_pb_a (.x(a), .y(pb_a));
    hw_nb u_nb_a (.x(a), .y(nb_a));
    hw_pb u_pb_b (.x(b), .y(pb_b));
    hw_nb u_nb_b (.x(b), .y(nb_b));

    /*
     * Carry generation per patent:
     *   PB(A): 0 when A=0, 2 when A>=1
     *   NB(B): 0 when B<=1, 2 when B=2
     *   AND: both 2 → carry when A>=1 AND B=2, i.e. (A,B) in {(1,2),(2,2)}
     *
     *   NB(A): 0 when A<=1, 2 when A=2
     *   PB(B): 0 when B=0, 2 when B>=1
     *   AND: both 2 → carry when A=2 AND B>=1, i.e. (A,B) in {(2,1),(2,2)}
     *
     *   Union: {(1,2),(2,1),(2,2)} → exactly A+B >= 3
     *
     * Output carry is in {0, 1} (Huawei encoding):
     *   0 → no carry, 1 → carry of 1
     */
    always @(*) begin
        if ((nb_a == `HW_2 && pb_b == `HW_2) ||
            (pb_a == `HW_2 && nb_b == `HW_2))
            c = `HW_1;  /* carry = 1 */
        else
            c = `HW_0;  /* carry = 0 */
    end
endmodule

/* ===================================================================
 * THA — Ternary Half-Adder (Patent Fig. 6, Claims 8-10)
 *
 * Inputs:  A[1:0], B[1:0]
 * Outputs: sum[1:0] = (A + B) mod 3
 *          carry[1:0] = floor((A + B) / 3)   (0 or 1)
 *
 * Structure: Tsum(A,B) → sum, Carry(A,B) → carry
 * ===================================================================*/
module hw_tha (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] sum,
    output [1:0] carry
);
    hw_tsum u_tsum  (.a(a), .b(b), .s(sum));
    hw_carry u_carry (.a(a), .b(b), .c(carry));
endmodule

/* ===================================================================
 * TFA — Ternary Full-Adder (Patent Fig. 7, Claims 11-14)
 *
 * Inputs:  A, B, Cin (all [1:0])
 * Outputs: sum   = (A + B + Cin) mod 3
 *          carry = floor((A + B + Cin) / 3)   (0 or 1)
 *
 * Two-stage cascade:
 *   Stage 1: THA(A, B)        → SUM_AB, Carry_AB
 *   Stage 2: THA₂(SUM_AB, C)  → SUM_ABC, Carry_SUM
 *   Final carry: OR(Carry_AB, Carry_SUM)
 *
 * Note: The patent proves that Carry_AB and Carry_SUM cannot both
 * be 1 simultaneously (since A,B,C ∈ {0,1,2} → max sum = 6 < 9),
 * so OR suffices for carry combination.
 *
 * Stage 2 optimization (Fig. 8): Since carry from stage 1 is always
 * 0 or 1 (never 2), the second-stage THA only needs the PB/INC path,
 * eliminating the DEC gate — saves 9 transistors.
 * ===================================================================*/
module hw_tfa (
    input  [1:0] a,
    input  [1:0] b,
    input  [1:0] cin,
    output [1:0] sum,
    output reg [1:0] carry
);
    wire [1:0] sum_ab, carry_ab;
    wire [1:0] sum_abc, carry_sum;

    /* Stage 1: THA(A, B) */
    hw_tha u_tha1 (.a(a), .b(b), .sum(sum_ab), .carry(carry_ab));

    /* Stage 2: THA(SUM_AB, Cin) - optimised for Cin ∈ {0, 1} */
    hw_tha u_tha2 (.a(sum_ab), .b(cin), .sum(sum_abc), .carry(carry_sum));

    assign sum = sum_abc;

    /* Carry combination: OR since both cannot be 1 simultaneously */
    always @(*) begin
        if (carry_ab != `HW_0 || carry_sum != `HW_0)
            carry = `HW_1;
        else
            carry = `HW_0;
    end
endmodule

/* ===================================================================
 * TMul — Exact 1-Trit Multiplier (Patent Claim 15)
 *
 * Truth table (Huawei encoding 0,1,2):
 *   A\B | 0 | 1 | 2
 *   ----+---+---+---
 *    0  | 0 | 0 | 0
 *    1  | 0 | 1 | 2
 *    2  | 0 | 2 | 1
 *
 * Note: In balanced ternary, this is:
 *   (-1)*(-1) = +1  ↔  Huawei: 0*0=0 ... different mapping!
 *
 * The Huawei table represents unbalanced multiplication mod 3:
 *   product = (A * B) mod 3 for {0,1,2}
 *   carry   = floor((A * B) / 3) → always 0 for 1-trit
 *
 * Since 2*2 = 4 = 1*3 + 1, product is 1 with carry 1.
 * The exact multiplier captures this carry.
 * ===================================================================*/
module hw_tmul (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] product,
    output reg [1:0] carry
);
    always @(*) begin
        case ({a, b})
            {`HW_0, `HW_0}: begin product = `HW_0; carry = `HW_0; end
            {`HW_0, `HW_1}: begin product = `HW_0; carry = `HW_0; end
            {`HW_0, `HW_2}: begin product = `HW_0; carry = `HW_0; end
            {`HW_1, `HW_0}: begin product = `HW_0; carry = `HW_0; end
            {`HW_1, `HW_1}: begin product = `HW_1; carry = `HW_0; end
            {`HW_1, `HW_2}: begin product = `HW_2; carry = `HW_0; end
            {`HW_2, `HW_0}: begin product = `HW_0; carry = `HW_0; end
            {`HW_2, `HW_1}: begin product = `HW_2; carry = `HW_0; end
            {`HW_2, `HW_2}: begin product = `HW_1; carry = `HW_1; end /* 2*2=4=1*3+1 */
            default:         begin product = `HW_0; carry = `HW_0; end
        endcase
    end
endmodule

/* ===================================================================
 * ATMul — Approximate 1-Trit Multiplier (Patent Claims 16-18)
 *
 * Same as TMul EXCEPT: when both inputs equal 2, the carry is
 * ignored (set to 0).  Product at (2,2) remains 1.
 *
 *   A\B | 0 | 1 | 2
 *   ----+---+---+---
 *    0  | 0 | 0 | 0
 *    1  | 0 | 1 | 2
 *    2  | 0 | 2 | 1*  (* carry forced to 0 instead of 1)
 *
 * Error: At (2,2), true product is 4, AT gives 1 → error = 3.
 * In balanced ternary: (+1)*(+1)=+1 carry +1 → AT gives +1 carry 0.
 *
 * This saves power by not propagating the carry for AI/ML workloads
 * where small approximation errors are acceptable.
 * ===================================================================*/
module hw_atmul (
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] product,
    output reg [1:0] carry
);
    always @(*) begin
        case ({a, b})
            {`HW_0, `HW_0}: begin product = `HW_0; carry = `HW_0; end
            {`HW_0, `HW_1}: begin product = `HW_0; carry = `HW_0; end
            {`HW_0, `HW_2}: begin product = `HW_0; carry = `HW_0; end
            {`HW_1, `HW_0}: begin product = `HW_0; carry = `HW_0; end
            {`HW_1, `HW_1}: begin product = `HW_1; carry = `HW_0; end
            {`HW_1, `HW_2}: begin product = `HW_2; carry = `HW_0; end
            {`HW_2, `HW_0}: begin product = `HW_0; carry = `HW_0; end
            {`HW_2, `HW_1}: begin product = `HW_2; carry = `HW_0; end
            {`HW_2, `HW_2}: begin product = `HW_1; carry = `HW_0; end /* APPROXIMATE: carry forced 0 */
            default:         begin product = `HW_0; carry = `HW_0; end
        endcase
    end
endmodule

/* ===================================================================
 * Compensation Units (Patent Claims 19-22)
 *
 * +6 Compensation: Add 6 to the partial product by setting P1 += 2
 *   In ternary: 6 = 2*3¹ + 0*3⁰, so add 2 to the 3¹ position
 *
 * +9 Compensation: Add 9 to the partial product by setting P2 += 1
 *   In ternary: 9 = 1*3² + 0*3¹ + 0*3⁰, so add 1 to the 3² position
 * ===================================================================*/
module hw_comp6 (
    input  [1:0] p1_in,   /* P1 digit (3¹ position) */
    output [1:0] p1_out   /* P1 after +2 compensation */
);
    hw_tsum u_add (.a(p1_in), .b(`HW_2), .s(p1_out));
endmodule

module hw_comp9 (
    input  [1:0] p2_in,   /* P2 digit (3² position) */
    output [1:0] p2_out   /* P2 after +1 compensation */
);
    hw_tsum u_add (.a(p2_in), .b(`HW_1), .s(p2_out));
endmodule

/* ===================================================================
 * 2-trit × 2-trit Multiplier (Patent Fig. 11b, Fig. 13)
 *
 * Inputs:  A = A1·3 + A0,  B = B1·3 + B0
 * Output:  P = P3·27 + P2·9 + P1·3 + P0  (4 trits)
 *
 * Partial products:
 *   A0*B0 at position 0    (TMul — exact, for MSB accuracy)
 *   A0*B1 at position 1    (ATMul — approximate)
 *   A1*B0 at position 1    (ATMul — approximate)
 *   A1*B1 at position 2    (ATMul — approximate)
 *
 * Combination (per patent):
 *   P0 = product(A0*B0)
 *   T1 = Tsum(product(A0*B1), product(A1*B0))
 *   (P1, C1) = THA(T1, carry(A0*B0))
 *   (P2, C2) = THA(product(A1*B1), C1)
 *   P3 = carry(A1*B1)  — but only for exact; ATMul has no carry at (2,2)
 *
 * Compensation applied to P1 (+6) or P2 (+9) to reduce error.
 * ===================================================================*/
module hw_mul2x2 (
    input  [3:0] a,       /* A = {A1, A0}, each trit 2 bits, MST first */
    input  [3:0] b,       /* B = {B1, B0} */
    input  [1:0] comp,    /* 00=none, 01=+6, 10=+9 */
    output [7:0] p        /* P = {P3, P2, P1, P0}, 4 trits */
);
    wire [1:0] a0 = a[1:0];
    wire [1:0] a1 = a[3:2];
    wire [1:0] b0 = b[1:0];
    wire [1:0] b1 = b[3:2];

    /* Partial products */
    wire [1:0] pp_a0b0_prod, pp_a0b0_carry;  /* TMul (exact) */
    wire [1:0] pp_a0b1_prod, pp_a0b1_carry;  /* ATMul */
    wire [1:0] pp_a1b0_prod, pp_a1b0_carry;  /* ATMul */
    wire [1:0] pp_a1b1_prod, pp_a1b1_carry;  /* ATMul */

    hw_tmul  u_pp00 (.a(a0), .b(b0), .product(pp_a0b0_prod), .carry(pp_a0b0_carry));
    hw_atmul u_pp01 (.a(a0), .b(b1), .product(pp_a0b1_prod), .carry(pp_a0b1_carry));
    hw_atmul u_pp10 (.a(a1), .b(b0), .product(pp_a1b0_prod), .carry(pp_a1b0_carry));
    hw_atmul u_pp11 (.a(a1), .b(b1), .product(pp_a1b1_prod), .carry(pp_a1b1_carry));

    /* P0 = product of A0*B0 */
    wire [1:0] p0 = pp_a0b0_prod;

    /* Sum partial products at position 1 */
    wire [1:0] t1;   /* Tsum of the two position-1 partial products */
    hw_tsum u_t1 (.a(pp_a0b1_prod), .b(pp_a1b0_prod), .s(t1));

    /* THA: combine T1 with carry from A0*B0 */
    wire [1:0] p1_raw, c1;
    hw_tha u_tha1 (.a(t1), .b(pp_a0b0_carry), .sum(p1_raw), .carry(c1));

    /* Apply compensation to P1 (+6 means P1 += 2) */
    wire [1:0] p1_comp6;
    hw_comp6 u_comp6 (.p1_in(p1_raw), .p1_out(p1_comp6));
    wire [1:0] p1 = (comp == 2'b01) ? p1_comp6 : p1_raw;

    /* THA: combine A1*B1 product with C1 */
    wire [1:0] p2_raw, c2;
    hw_tha u_tha2 (.a(pp_a1b1_prod), .b(c1), .sum(p2_raw), .carry(c2));

    /* Apply compensation to P2 (+9 means P2 += 1) */
    wire [1:0] p2_comp9;
    hw_comp9 u_comp9 (.p2_in(p2_raw), .p2_out(p2_comp9));
    wire [1:0] p2 = (comp == 2'b10) ? p2_comp9 : p2_raw;

    /* P3 = carry from A1*B1 (always 0 for ATMul at 2×2) + C2 */
    wire [1:0] p3_sum;
    hw_tsum u_p3 (.a(pp_a1b1_carry), .b(c2), .s(p3_sum));
    wire [1:0] p3 = p3_sum;

    assign p = {p3, p2, p1, p0};
endmodule

/* ===================================================================
 * Multi-trit Word Adder (chained full-adders)
 *
 * Adds two N-trit words using a ripple-carry chain of TFA circuits.
 * Parameterized width for use in the 6×6 multiplier.
 * ===================================================================*/
module hw_word_adder #(
    parameter WIDTH = 6
)(
    input  [2*WIDTH-1:0] a,
    input  [2*WIDTH-1:0] b,
    input  [1:0]         cin,
    output [2*WIDTH-1:0] sum,
    output [1:0]         cout
);
    wire [1:0] carry [0:WIDTH];
    assign carry[0] = cin;

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : adder_chain
            hw_tfa u_tfa (
                .a(a[2*i+1 : 2*i]),
                .b(b[2*i+1 : 2*i]),
                .cin(carry[i]),
                .sum(sum[2*i+1 : 2*i]),
                .carry(carry[i+1])
            );
        end
    endgenerate

    assign cout = carry[WIDTH];
endmodule

/* ===================================================================
 * 6-trit × 6-trit Multiplier (Patent Fig. 14)
 *
 * Decomposes each 6-trit operand into three 2-trit blocks:
 *   A = A_H·9² + A_M·9¹ + A_L·9⁰
 *   B = B_H·9² + B_M·9¹ + B_L·9⁰
 *
 * Computes 9 partial products (2×2 each), accumulates with
 * weighted shifts using exact-mode adders.
 *
 * Product width: 12 trits (24 bits in 2-bit encoding).
 * ===================================================================*/
module hw_mul6x6 (
    input  [11:0] a,       /* 6 trits: {A5,A4,A3,A2,A1,A0} */
    input  [11:0] b,       /* 6 trits: {B5,B4,B3,B2,B1,B0} */
    input  [1:0]  comp,    /* 00=none, 01=+6, 10=+9 */
    output [23:0] p        /* 12 trits result */
);
    /* Decompose into 2-trit blocks */
    wire [3:0] a_l = a[3:0];    /* A[1:0], trits 0-1 */
    wire [3:0] a_m = a[7:4];    /* A[3:2], trits 2-3 */
    wire [3:0] a_h = a[11:8];   /* A[5:4], trits 4-5 */
    wire [3:0] b_l = b[3:0];
    wire [3:0] b_m = b[7:4];
    wire [3:0] b_h = b[11:8];

    /* 9 partial products (2×2 each) */
    wire [7:0] pp_ll, pp_lm, pp_lh;
    wire [7:0] pp_ml, pp_mm, pp_mh;
    wire [7:0] pp_hl, pp_hm, pp_hh;

    /* A_L * B_L at position 0 (shift 0 trits) */
    hw_mul2x2 u_ll (.a(a_l), .b(b_l), .comp(comp), .p(pp_ll));
    /* A_L * B_M at position 2 (shift 2 trits) */
    hw_mul2x2 u_lm (.a(a_l), .b(b_m), .comp(comp), .p(pp_lm));
    /* A_L * B_H at position 4 (shift 4 trits) */
    hw_mul2x2 u_lh (.a(a_l), .b(b_h), .comp(comp), .p(pp_lh));
    /* A_M * B_L at position 2 */
    hw_mul2x2 u_ml (.a(a_m), .b(b_l), .comp(comp), .p(pp_ml));
    /* A_M * B_M at position 4 */
    hw_mul2x2 u_mm (.a(a_m), .b(b_m), .comp(comp), .p(pp_mm));
    /* A_M * B_H at position 6 */
    hw_mul2x2 u_mh (.a(a_m), .b(b_h), .comp(comp), .p(pp_mh));
    /* A_H * B_L at position 4 */
    hw_mul2x2 u_hl (.a(a_h), .b(b_l), .comp(comp), .p(pp_hl));
    /* A_H * B_M at position 6 */
    hw_mul2x2 u_hm (.a(a_h), .b(b_m), .comp(comp), .p(pp_hm));
    /* A_H * B_H at position 8 */
    hw_mul2x2 u_hh (.a(a_h), .b(b_h), .comp(comp), .p(pp_hh));

    /*
     * Accumulate partial products with positional shifts.
     * Each pp is 4 trits (8 bits).  We zero-pad and align to 12-trit
     * (24-bit) words before adding.
     */
    wire [23:0] aligned_ll = {16'b0, pp_ll};                               /* pos 0 */
    wire [23:0] aligned_lm = {12'b0, pp_lm, 4'b0};                         /* pos 2 */
    wire [23:0] aligned_lh = {8'b0,  pp_lh, 8'b0};                         /* pos 4 */
    wire [23:0] aligned_ml = {12'b0, pp_ml, 4'b0};                         /* pos 2 */
    wire [23:0] aligned_mm = {8'b0,  pp_mm, 8'b0};                         /* pos 4 */
    wire [23:0] aligned_mh = {4'b0,  pp_mh, 12'b0};                        /* pos 6 */
    wire [23:0] aligned_hl = {8'b0,  pp_hl, 8'b0};                         /* pos 4 */
    wire [23:0] aligned_hm = {4'b0,  pp_hm, 12'b0};                        /* pos 6 */
    wire [23:0] aligned_hh = {pp_hh, 16'b0};                               /* pos 8 */

    /*
     * Tree accumulation using word adders.
     * 9 partial products → 4 stages of pairwise addition.
     */
    wire [23:0] sum_01, sum_23, sum_45, sum_67;
    wire [1:0]  co_01, co_23, co_45, co_67;

    /* Stage 1: pair up */
    hw_word_adder #(.WIDTH(12)) u_s1a (.a(aligned_ll), .b(aligned_lm),
                                        .cin(`HW_0), .sum(sum_01), .cout(co_01));
    hw_word_adder #(.WIDTH(12)) u_s1b (.a(aligned_lh), .b(aligned_ml),
                                        .cin(`HW_0), .sum(sum_23), .cout(co_23));
    hw_word_adder #(.WIDTH(12)) u_s1c (.a(aligned_mm), .b(aligned_mh),
                                        .cin(`HW_0), .sum(sum_45), .cout(co_45));
    hw_word_adder #(.WIDTH(12)) u_s1d (.a(aligned_hl), .b(aligned_hm),
                                        .cin(`HW_0), .sum(sum_67), .cout(co_67));

    /* Stage 2: reduce 4+1 → 3 */
    wire [23:0] sum_0123, sum_4567;
    wire [1:0]  co_0123, co_4567;
    hw_word_adder #(.WIDTH(12)) u_s2a (.a(sum_01), .b(sum_23),
                                        .cin(`HW_0), .sum(sum_0123), .cout(co_0123));
    hw_word_adder #(.WIDTH(12)) u_s2b (.a(sum_45), .b(sum_67),
                                        .cin(`HW_0), .sum(sum_4567), .cout(co_4567));

    /* Stage 3: add remaining hh */
    wire [23:0] sum_45678;
    wire [1:0]  co_45678;
    hw_word_adder #(.WIDTH(12)) u_s3 (.a(sum_4567), .b(aligned_hh),
                                       .cin(`HW_0), .sum(sum_45678), .cout(co_45678));

    /* Stage 4: final sum */
    wire [1:0] co_final;
    hw_word_adder #(.WIDTH(12)) u_s4 (.a(sum_0123), .b(sum_45678),
                                       .cin(`HW_0), .sum(p), .cout(co_final));
endmodule

/* ===================================================================
 * Top-Level ALU Module with MMIO Register Interface
 *
 * Wraps all circuits with a register-mapped interface matching the
 * MMIO layout in huawei_mmio.h.  For Verilog simulation only.
 * ===================================================================*/
module hw_cn119652311a_alu (
    input         clk,
    input         rst_n,

    /* Simplified bus interface */
    input         wr_en,
    input         rd_en,
    input  [11:0] addr,    /* Register address (12-bit offset) */
    input  [31:0] wr_data,
    output reg [31:0] rd_data,
    output reg    irq
);

    /* ---- Internal registers ---- */
    reg [31:0] chip_id;
    reg [31:0] features;
    reg [31:0] vdd_ctrl;
    reg [31:0] vth_cfg;

    reg [31:0] operand_a;
    reg [31:0] operand_b;
    reg [31:0] operand_c;
    reg [31:0] operand_d;

    reg [31:0] alu_cmd;
    reg [31:0] alu_status;
    reg [31:0] alu_result;

    reg [31:0] gate_op;
    reg [31:0] gate_result;

    reg [31:0] approx_cfg;
    reg [31:0] comp_mode;

    reg [31:0] irq_status;
    reg [31:0] irq_enable;

    /* ---- ALU results for wide multiply ---- */
    reg [31:0] wide_result [0:11];

    /* ---- Combinational ALU output wires ---- */
    wire [1:0] inc_out, dec_out, nti_out, pti_out;
    wire [1:0] tsum_out;
    wire [1:0] tha_sum, tha_carry;
    wire [1:0] tfa_sum, tfa_carry;
    wire [1:0] tmul_prod, tmul_carry;
    wire [1:0] atmul_prod, atmul_carry;
    wire [7:0] mul2x2_out;
    wire [23:0] mul6x6_out;

    /* Gate units */
    hw_inc  u_inc  (.x(operand_a[1:0]), .y(inc_out));
    hw_dec  u_dec  (.x(operand_a[1:0]), .y(dec_out));
    hw_nti  u_nti  (.x(operand_a[1:0]), .y(nti_out));
    hw_pti  u_pti  (.x(operand_a[1:0]), .y(pti_out));

    /* Arithmetic units */
    hw_tsum  u_tsum  (.a(operand_a[1:0]), .b(operand_b[1:0]), .s(tsum_out));
    hw_tha   u_tha   (.a(operand_a[1:0]), .b(operand_b[1:0]),
                      .sum(tha_sum), .carry(tha_carry));
    hw_tfa   u_tfa   (.a(operand_a[1:0]), .b(operand_b[1:0]),
                      .cin(operand_c[1:0]), .sum(tfa_sum), .carry(tfa_carry));
    hw_tmul  u_tmul  (.a(operand_a[1:0]), .b(operand_b[1:0]),
                      .product(tmul_prod), .carry(tmul_carry));
    hw_atmul u_atmul (.a(operand_a[1:0]), .b(operand_b[1:0]),
                      .product(atmul_prod), .carry(atmul_carry));

    /* Wide multipliers */
    hw_mul2x2 u_mul2x2 (.a(operand_a[3:0]), .b(operand_b[3:0]),
                         .comp(comp_mode[1:0]), .p(mul2x2_out));
    hw_mul6x6 u_mul6x6 (.a(operand_a[11:0]), .b(operand_b[11:0]),
                         .comp(comp_mode[1:0]), .p(mul6x6_out));

    /* ---- Register addresses (match huawei_mmio.h) ---- */
    localparam A_CHIP_ID    = 12'h000;
    localparam A_FEATURES   = 12'h004;
    localparam A_VDD_CTRL   = 12'h010;
    localparam A_VTH_CFG    = 12'h014;
    localparam A_GATE_OP    = 12'h020;
    localparam A_GATE_RESULT= 12'h024;
    localparam A_GATE_STATUS= 12'h028;
    localparam A_OP_A       = 12'h040;
    localparam A_OP_B       = 12'h044;
    localparam A_OP_C       = 12'h048;
    localparam A_OP_D       = 12'h04C;
    localparam A_ALU_CMD    = 12'h080;
    localparam A_ALU_STATUS = 12'h084;
    localparam A_ALU_RESULT = 12'h088;
    localparam A_APPROX_CFG = 12'h0C0;
    localparam A_COMP_MODE  = 12'h0C4;
    localparam A_IRQ_STATUS = 12'h200;
    localparam A_IRQ_ENABLE = 12'h204;
    localparam A_IRQ_CLEAR  = 12'h208;

    /* ALU command opcodes (matching huawei_mmio.h) */
    localparam OP_TSUM  = 4'd1;
    localparam OP_THA   = 4'd2;
    localparam OP_TFA   = 4'd3;
    localparam OP_TMUL  = 4'd4;
    localparam OP_ATMUL = 4'd5;
    localparam OP_WMUL2 = 4'd6;
    localparam OP_WMUL6 = 4'd7;
    localparam OP_COMP6 = 4'd8;
    localparam OP_COMP9 = 4'd9;

    /* ---- Initialisation ---- */
    integer j;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            chip_id    <= 32'h48570001;  /* "HW" + rev 1 */
            features   <= 32'h000001FF;  /* All features present */
            vdd_ctrl   <= 32'd1000;      /* 1.0 V */
            vth_cfg    <= {8'd65, 8'd40, 8'd25, 8'd0};
            alu_status <= 32'h00000001;  /* Ready */
            alu_result <= 32'h0;
            gate_result<= 32'h0;
            irq_status <= 32'h0;
            irq_enable <= 32'h0;
            irq        <= 1'b0;
            approx_cfg <= 32'h0;
            comp_mode  <= 32'h0;
            operand_a  <= 32'h0;
            operand_b  <= 32'h0;
            operand_c  <= 32'h0;
            operand_d  <= 32'h0;
            alu_cmd    <= 32'h0;
            gate_op    <= 32'h0;
            for (j = 0; j < 12; j = j + 1)
                wide_result[j] <= 32'h0;
        end else begin

            /* ---- Write handling ---- */
            if (wr_en) begin
                case (addr)
                    A_VDD_CTRL:  vdd_ctrl  <= wr_data;
                    A_VTH_CFG:   vth_cfg   <= wr_data;
                    A_OP_A:      operand_a <= wr_data;
                    A_OP_B:      operand_b <= wr_data;
                    A_OP_C:      operand_c <= wr_data;
                    A_OP_D:      operand_d <= wr_data;
                    A_APPROX_CFG:approx_cfg<= wr_data;
                    A_COMP_MODE: comp_mode <= wr_data;
                    A_IRQ_ENABLE:irq_enable<= wr_data;
                    A_IRQ_CLEAR: irq_status<= irq_status & ~wr_data;

                    A_GATE_OP: begin
                        gate_op <= wr_data;
                        /* Execute gate operation immediately */
                        case (wr_data[7:4])
                            4'h1: gate_result <= {30'b0, inc_out};
                            4'h2: gate_result <= {30'b0, dec_out};
                            4'h3: gate_result <= {30'b0, nti_out};
                            4'h4: gate_result <= {30'b0, pti_out};
                            default: gate_result <= 32'h0;
                        endcase
                    end

                    A_ALU_CMD: begin
                        alu_cmd <= wr_data;
                        alu_status <= 32'h00000002; /* Busy */

                        /* Execute in next cycle — combinational for now */
                        case (wr_data[3:0])
                            OP_TSUM: begin
                                alu_result <= {30'b0, tsum_out};
                                alu_status <= 32'h00000001;
                            end
                            OP_THA: begin
                                alu_result <= {28'b0, tha_carry, tha_sum};
                                alu_status <= 32'h00000001;
                            end
                            OP_TFA: begin
                                alu_result <= {28'b0, tfa_carry, tfa_sum};
                                alu_status <= 32'h00000001;
                            end
                            OP_TMUL: begin
                                alu_result <= {28'b0, tmul_carry, tmul_prod};
                                alu_status <= 32'h00000001;
                            end
                            OP_ATMUL: begin
                                alu_result <= {28'b0, atmul_carry, atmul_prod};
                                alu_status <= 32'h00000001;
                            end
                            OP_WMUL2: begin
                                alu_result <= {24'b0, mul2x2_out};
                                alu_status <= 32'h00000001;
                            end
                            OP_WMUL6: begin
                                /* Store 12-trit result in wide_result registers */
                                wide_result[0] <= {30'b0, mul6x6_out[1:0]};
                                wide_result[1] <= {30'b0, mul6x6_out[3:2]};
                                wide_result[2] <= {30'b0, mul6x6_out[5:4]};
                                wide_result[3] <= {30'b0, mul6x6_out[7:6]};
                                wide_result[4] <= {30'b0, mul6x6_out[9:8]};
                                wide_result[5] <= {30'b0, mul6x6_out[11:10]};
                                wide_result[6] <= {30'b0, mul6x6_out[13:12]};
                                wide_result[7] <= {30'b0, mul6x6_out[15:14]};
                                wide_result[8] <= {30'b0, mul6x6_out[17:16]};
                                wide_result[9] <= {30'b0, mul6x6_out[19:18]};
                                wide_result[10]<= {30'b0, mul6x6_out[21:20]};
                                wide_result[11]<= {30'b0, mul6x6_out[23:22]};
                                alu_result <= mul6x6_out[31:0]; /* lower 16 bits */
                                alu_status <= 32'h00000001;
                            end
                            default: begin
                                alu_result <= 32'h0;
                                alu_status <= 32'h00000001;
                            end
                        endcase

                        /* Raise interrupt if enabled */
                        if (irq_enable[0]) begin
                            irq_status[0] <= 1'b1;
                            irq <= 1'b1;
                        end
                    end
                endcase
            end

            /* Clear IRQ when all status bits cleared */
            if (irq_status == 32'h0)
                irq <= 1'b0;
        end
    end

    /* ---- Read handling ---- */
    always @(*) begin
        rd_data = 32'h0;
        if (rd_en) begin
            case (addr)
                A_CHIP_ID:    rd_data = chip_id;
                A_FEATURES:   rd_data = features;
                A_VDD_CTRL:   rd_data = vdd_ctrl;
                A_VTH_CFG:    rd_data = vth_cfg;
                A_GATE_OP:    rd_data = gate_op;
                A_GATE_RESULT:rd_data = gate_result;
                A_GATE_STATUS:rd_data = 32'h00000001;  /* Always ready */
                A_OP_A:       rd_data = operand_a;
                A_OP_B:       rd_data = operand_b;
                A_OP_C:       rd_data = operand_c;
                A_OP_D:       rd_data = operand_d;
                A_ALU_CMD:    rd_data = alu_cmd;
                A_ALU_STATUS: rd_data = alu_status;
                A_ALU_RESULT: rd_data = alu_result;
                A_APPROX_CFG: rd_data = approx_cfg;
                A_COMP_MODE:  rd_data = comp_mode;
                A_IRQ_STATUS: rd_data = irq_status;
                A_IRQ_ENABLE: rd_data = irq_enable;
                /* Wide result registers at 0x090 + i*4 */
                12'h090: rd_data = wide_result[0];
                12'h094: rd_data = wide_result[1];
                12'h098: rd_data = wide_result[2];
                12'h09C: rd_data = wide_result[3];
                12'h0A0: rd_data = wide_result[4];
                12'h0A4: rd_data = wide_result[5];
                12'h0A8: rd_data = wide_result[6];
                12'h0AC: rd_data = wide_result[7];
                12'h0B0: rd_data = wide_result[8];
                12'h0B4: rd_data = wide_result[9];
                12'h0B8: rd_data = wide_result[10];
                12'h0BC: rd_data = wide_result[11];
                default:      rd_data = 32'h0;
            endcase
        end
    end

endmodule
