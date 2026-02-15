/**
 * @file trit_k3_gates.v
 * @brief seT6 Jones K3 Kleene Logic Gates — Consensus & Accept-Anything
 *
 * Synthesisable Verilog implementation of the K3 (Kleene three-valued logic)
 * gate primitives from Jones, "Completeness of Kleene Logic".
 *
 * Encoding (matches trit_art9_pipeline.v):
 *   2'b00 = T (-1, false)
 *   2'b01 = 0 ( 0, unknown)
 *   2'b10 = 1 (+1, true)
 *
 * Operators:
 *   Consensus  (⊠): true if both true, false if both false, else unknown
 *   Accept-Any (⊞): true if either true, false if either false, else unknown
 *                    (dual of consensus)
 *
 * These form a complete functional basis for K3 together with negation.
 *
 * Reference: Jones, "Completeness of Kleene Logic"
 *
 * SPDX-License-Identifier: GPL-2.0
 */

module ternary_k3_consensus (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] out
);
    /* Consensus: both agree → that value; otherwise unknown (01) */
    assign out = (a == b)   ? a    :  /* agree → that value */
                              2'b01;  /* disagree → unknown */
endmodule

module ternary_k3_accept_any (
    input  [1:0] a,
    input  [1:0] b,
    output [1:0] out
);
    /* Accept-anything (dual of consensus):
     * If either is true (10), result is true (unless both are non-unknown and disagree)
     * If either is false (00), result is false (unless both non-unknown and disagree)
     * If both unknown → unknown
     * If a != unknown, pick a; if b != unknown, pick b; if both non-unknown and differ → unknown */
    assign out = (a == 2'b01) ? b :    /* a unknown → take b */
                 (b == 2'b01) ? a :    /* b unknown → take a */
                 (a == b)     ? a :    /* agree → that value */
                                2'b01; /* both non-unknown but disagree → unknown */
endmodule

module ternary_k3_negate (
    input  [1:0] a,
    output [1:0] out
);
    /* Negation: T→1, 0→0, 1→T */
    assign out = (a == 2'b00) ? 2'b10 :
                 (a == 2'b10) ? 2'b00 :
                                2'b01;
endmodule

/* Combined K3 logic unit — selects between consensus, accept-any, negate */
module ternary_k3_alu (
    input  [1:0] a,
    input  [1:0] b,
    input  [1:0] op,    /* 00=consensus, 01=accept_any, 10=negate(a) */
    output [1:0] out
);
    wire [1:0] cons_out, accept_out, neg_out;

    ternary_k3_consensus u_cons (.a(a), .b(b), .out(cons_out));
    ternary_k3_accept_any u_acc (.a(a), .b(b), .out(accept_out));
    ternary_k3_negate    u_neg (.a(a), .out(neg_out));

    assign out = (op == 2'b00) ? cons_out :
                 (op == 2'b01) ? accept_out :
                 (op == 2'b10) ? neg_out :
                                 2'b01; /* default: unknown */
endmodule
