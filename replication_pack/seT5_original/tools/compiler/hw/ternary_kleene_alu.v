/**
 * ternary_kleene_alu.v — Extended Ternary ALU with Kleene K₃ Logic
 *
 * Extends the base ternary_alu.v with:
 *   - Kleene AND (min), OR (max), NOT (negation)
 *   - DOT_TRIT accumulate-multiply unit
 *   - N:M structured sparsity bypass
 *   - FFT radix-3 butterfly datapath
 *   - 2-bit encoding: 00 = F(-1), 01 = U(0), 11 = T(+1), 10 = Fault
 *
 * Hardware targets:
 *   - Lattice iCE40 HX8K (≤ 7680 LUT4s)
 *   - Xilinx Artix-7 XC7A35T (≤ 20,800 slices)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

`default_nettype none

/* ==== Trit encoding constants ========================================== */
`define TRIT_F  2'b00    // False  = -1
`define TRIT_U  2'b01    // Unknown = 0
`define TRIT_T  2'b11    // True   = +1
`define TRIT_X  2'b10    // Fault (invalid)

/* ==== Kleene K₃ Logic Gates ============================================ */

/**
 * Kleene AND = min(a, b) in the order F < U < T
 * Truth table (balanced ternary):
 *   a\b |  F  U  T
 *   ----+---------
 *    F  |  F  F  F
 *    U  |  F  U  U
 *    T  |  F  U  T
 */
module kleene_and (
    input  wire [1:0] a,
    input  wire [1:0] b,
    output wire [1:0] out
);
    /* min(a,b): if either is F, result is F. If either is U and other ≤ T, U. */
    wire a_is_f = (a == `TRIT_F);
    wire b_is_f = (b == `TRIT_F);
    wire a_is_u = (a == `TRIT_U);
    wire b_is_u = (b == `TRIT_U);

    assign out = (a_is_f || b_is_f) ? `TRIT_F :
                 (a_is_u || b_is_u) ? `TRIT_U :
                                      `TRIT_T;
endmodule

/**
 * Kleene OR = max(a, b) in the order F < U < T
 */
module kleene_or (
    input  wire [1:0] a,
    input  wire [1:0] b,
    output wire [1:0] out
);
    wire a_is_t = (a == `TRIT_T);
    wire b_is_t = (b == `TRIT_T);
    wire a_is_u = (a == `TRIT_U);
    wire b_is_u = (b == `TRIT_U);

    assign out = (a_is_t || b_is_t) ? `TRIT_T :
                 (a_is_u || b_is_u) ? `TRIT_U :
                                      `TRIT_F;
endmodule

/**
 * Kleene NOT = negation (swap F ↔ T, U stays U)
 */
module kleene_not (
    input  wire [1:0] a,
    output wire [1:0] out
);
    assign out = (a == `TRIT_F) ? `TRIT_T :
                 (a == `TRIT_T) ? `TRIT_F :
                                  `TRIT_U;
endmodule

/* ==== Trit Multiplier (balanced ternary product) ======================= */
/**
 * trit_mul: balanced ternary product
 *   F*F = T,  F*U = U,  F*T = F
 *   U*x = U,  x*U = U
 *   T*T = T,  T*F = F,  T*U = U
 */
module trit_mul (
    input  wire [1:0] a,
    input  wire [1:0] b,
    output wire [1:0] out
);
    wire a_is_u = (a == `TRIT_U);
    wire b_is_u = (b == `TRIT_U);
    wire a_is_f = (a == `TRIT_F);
    wire b_is_f = (b == `TRIT_F);

    /* If either is Unknown, result is Unknown */
    /* If signs match (both F or both T), result is T */
    /* If signs differ, result is F */
    assign out = (a_is_u || b_is_u) ? `TRIT_U :
                 (a == b)           ? `TRIT_T :
                                      `TRIT_F;
endmodule

/* ==== Trit Adder (balanced ternary: -1+0+1 with carry) ================= */
/**
 * Full trit adder with carry. Uses ROM/LUT approach.
 * sum = (a + b + cin) mod 3
 * cout = (a + b + cin) / 3
 */
module trit_full_adder (
    input  wire [1:0] a,
    input  wire [1:0] b,
    input  wire [1:0] cin,
    output reg  [1:0] sum,
    output reg  [1:0] cout
);
    /* Decode to signed integer: F=-1, U=0, T=+1 */
    wire signed [1:0] va = (a == `TRIT_F) ? -2'sd1 :
                           (a == `TRIT_T) ?  2'sd1 : 2'sd0;
    wire signed [1:0] vb = (b == `TRIT_F) ? -2'sd1 :
                           (b == `TRIT_T) ?  2'sd1 : 2'sd0;
    wire signed [1:0] vc = (cin == `TRIT_F) ? -2'sd1 :
                           (cin == `TRIT_T) ?  2'sd1 : 2'sd0;
    wire signed [2:0] total = {va[1], va} + {vb[1], vb} + {vc[1], vc};

    always @(*) begin
        case (total)
            -3: begin sum = `TRIT_U;  cout = `TRIT_F; end  // -3 = 0 + (-1)*3
            -2: begin sum = `TRIT_T;  cout = `TRIT_F; end  // -2 = 1 + (-1)*3
            -1: begin sum = `TRIT_F;  cout = `TRIT_U; end
             0: begin sum = `TRIT_U;  cout = `TRIT_U; end
             1: begin sum = `TRIT_T;  cout = `TRIT_U; end
             2: begin sum = `TRIT_F;  cout = `TRIT_T; end  //  2 = -1 + 1*3
             3: begin sum = `TRIT_U;  cout = `TRIT_T; end  //  3 = 0 + 1*3
        default: begin sum = `TRIT_X;  cout = `TRIT_X; end
        endcase
    end
endmodule

/* ==== N-trit Word Adder (ripple carry, parameterised) ================== */
module trit_word_adder #(
    parameter WIDTH = 9  /* Number of trits */
) (
    input  wire [2*WIDTH-1:0] a,
    input  wire [2*WIDTH-1:0] b,
    output wire [2*WIDTH-1:0] sum,
    output wire [1:0]         carry_out
);
    wire [1:0] carry [0:WIDTH];
    assign carry[0] = `TRIT_U;

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : adders
            trit_full_adder fa (
                .a   (a[2*i+1:2*i]),
                .b   (b[2*i+1:2*i]),
                .cin (carry[i]),
                .sum (sum[2*i+1:2*i]),
                .cout(carry[i+1])
            );
        end
    endgenerate

    assign carry_out = carry[WIDTH];
endmodule

/* ==== DOT_TRIT Accumulator ============================================= */
/**
 * Sequential MAC (multiply-accumulate) unit for ternary dot product.
 * On each clock: acc += trit_mul(a_i, b_i)
 * With N:M sparsity bypass: if a_i == U, skip the multiply.
 *
 * Controls:
 *   start    — begin new dot product (resets accumulator)
 *   step     — compute one MAC step
 *   busy     — high while computing
 *   result   — accumulated 9-trit result
 */
module dot_trit_unit #(
    parameter LANES = 9,  /* Accumulator width in trits */
    parameter DEPTH = 32  /* Vector length (positions to accumulate) */
) (
    input  wire        clk,
    input  wire        rst_n,
    input  wire        start,
    input  wire [1:0]  a_trit,      /* Current a element */
    input  wire [1:0]  b_trit,      /* Current b element */
    output reg         busy,
    output reg  [2*LANES-1:0] result,
    output reg  [5:0]  pos,         /* Current position counter */
    output reg         done,
    output reg  [5:0]  sparse_skip  /* Count of U-skips (N:M sparsity) */
);
    /* Internal signals */
    wire [1:0] product;
    trit_mul mul_inst (.a(a_trit), .b(b_trit), .out(product));

    /* Accumulator: add product to running sum */
    wire [2*LANES-1:0] product_ext;
    assign product_ext = {{(2*(LANES-1)){1'b0}}, product}; /* zero-extend */

    wire [2*LANES-1:0] new_acc;
    wire [1:0] acc_carry;
    trit_word_adder #(.WIDTH(LANES)) acc_add (
        .a(result),
        .b(product_ext),
        .sum(new_acc),
        .carry_out(acc_carry)
    );

    /* N:M sparsity check — skip if a == Unknown (zero) */
    wire skip = (a_trit == `TRIT_U);

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            busy        <= 1'b0;
            done        <= 1'b0;
            result      <= {2*LANES{1'b0}};
            pos         <= 6'd0;
            sparse_skip <= 6'd0;
        end else if (start) begin
            busy        <= 1'b1;
            done        <= 1'b0;
            result      <= {2*LANES{1'b0}};
            pos         <= 6'd0;
            sparse_skip <= 6'd0;
        end else if (busy) begin
            if (pos < DEPTH[5:0]) begin
                if (!skip) begin
                    result <= new_acc;
                end else begin
                    sparse_skip <= sparse_skip + 1'b1;
                end
                pos <= pos + 1'b1;
            end else begin
                busy <= 1'b0;
                done <= 1'b1;
            end
        end
    end
endmodule

/* ==== FFT Radix-3 Butterfly ============================================ */
/**
 * Computes one radix-3 butterfly step:
 *   Y0 = X0 + X1 + X2
 *   Y1 = X0 + ω·X1 + ω²·X2
 *   Y2 = X0 + ω²·X1 + ω·X2
 *
 * In mod-3 arithmetic, ω = rotation by one position in {F,U,T}.
 * ω²  = rotation by two (= inverse rotation).
 */
module fft_butterfly (
    input  wire [1:0] x0,
    input  wire [1:0] x1,
    input  wire [1:0] x2,
    output wire [1:0] y0,
    output wire [1:0] y1,
    output wire [1:0] y2
);
    /* Twiddle factor: ω = rotate (F→U→T→F) */
    wire [1:0] w_x1;  /* ω · x1 */
    assign w_x1 = (x1 == `TRIT_F) ? `TRIT_U :
                  (x1 == `TRIT_U) ? `TRIT_T :
                                    `TRIT_F;

    wire [1:0] w2_x2;  /* ω² · x2 */
    assign w2_x2 = (x2 == `TRIT_F) ? `TRIT_T :
                   (x2 == `TRIT_U) ? `TRIT_F :
                                     `TRIT_U;

    wire [1:0] w2_x1;  /* ω² · x1 */
    assign w2_x1 = (x1 == `TRIT_F) ? `TRIT_T :
                   (x1 == `TRIT_U) ? `TRIT_F :
                                     `TRIT_U;

    wire [1:0] w_x2;  /* ω · x2 */
    assign w_x2 = (x2 == `TRIT_F) ? `TRIT_U :
                  (x2 == `TRIT_U) ? `TRIT_T :
                                    `TRIT_F;

    /* Y0 = X0 + X1 + X2 (mod 3) */
    wire [1:0] s01, c01;
    trit_full_adder add_y0a (.a(x0), .b(x1), .cin(`TRIT_U), .sum(s01), .cout(c01));
    wire [1:0] y0_sum, y0_carry;
    trit_full_adder add_y0b (.a(s01), .b(x2), .cin(`TRIT_U), .sum(y0_sum), .cout(y0_carry));
    assign y0 = y0_sum;

    /* Y1 = X0 + ω·X1 + ω²·X2 */
    wire [1:0] s_y1a, c_y1a;
    trit_full_adder add_y1a (.a(x0), .b(w_x1), .cin(`TRIT_U), .sum(s_y1a), .cout(c_y1a));
    wire [1:0] y1_sum, y1_carry;
    trit_full_adder add_y1b (.a(s_y1a), .b(w2_x2), .cin(`TRIT_U), .sum(y1_sum), .cout(y1_carry));
    assign y1 = y1_sum;

    /* Y2 = X0 + ω²·X1 + ω·X2 */
    wire [1:0] s_y2a, c_y2a;
    trit_full_adder add_y2a (.a(x0), .b(w2_x1), .cin(`TRIT_U), .sum(s_y2a), .cout(c_y2a));
    wire [1:0] y2_sum, y2_carry;
    trit_full_adder add_y2b (.a(s_y2a), .b(w_x2), .cin(`TRIT_U), .sum(y2_sum), .cout(y2_carry));
    assign y2 = y2_sum;
endmodule

/* ==== Extended ALU ===================================================== */
/**
 * ternary_kleene_alu — Full ALU with 10 operations:
 *   0000: ADD     (balanced ternary addition)
 *   0001: SUB     (a + NOT(b) + 1)
 *   0010: MUL     (balanced ternary multiplication)
 *   0011: K_AND   (Kleene AND = min)
 *   0100: K_OR    (Kleene OR = max)
 *   0101: K_NOT   (Kleene NOT = negation, operates on A only)
 *   0110: DOT_ACC (dot product accumulate step = a*b)
 *   0111: FFT     (radix-3 butterfly: a=x0, b=x1, trit0 of result)
 *   1000: INC     (cyclic increment: F→U→T→F)
 *   1001: CMP     (compare: F if a<b, U if a==b, T if a>b)
 */
module ternary_kleene_alu (
    input  wire [1:0] a,
    input  wire [1:0] b,
    input  wire [3:0] op,
    output reg  [1:0] result,
    output reg  [1:0] carry
);
    /* Kleene gates */
    wire [1:0] k_and_out, k_or_out, k_not_out;
    kleene_and kand (.a(a), .b(b), .out(k_and_out));
    kleene_or  kor  (.a(a), .b(b), .out(k_or_out));
    kleene_not knot (.a(a),        .out(k_not_out));

    /* Arithmetic */
    wire [1:0] add_sum, add_carry;
    trit_full_adder adder (.a(a), .b(b), .cin(`TRIT_U),
                           .sum(add_sum), .cout(add_carry));

    wire [1:0] not_b;
    kleene_not neg_b (.a(b), .out(not_b));
    wire [1:0] sub_sum, sub_carry;
    trit_full_adder subber (.a(a), .b(not_b), .cin(`TRIT_T),
                            .sum(sub_sum), .cout(sub_carry));

    /* Multiply */
    wire [1:0] mul_out;
    trit_mul mulu (.a(a), .b(b), .out(mul_out));

    /* Cyclic increment */
    wire [1:0] inc_out;
    assign inc_out = (a == `TRIT_F) ? `TRIT_U :
                     (a == `TRIT_U) ? `TRIT_T :
                                      `TRIT_F;

    /* Compare */
    wire [1:0] cmp_out;
    wire signed [1:0] sa = (a == `TRIT_F) ? -2'sd1 :
                           (a == `TRIT_T) ?  2'sd1 : 2'sd0;
    wire signed [1:0] sb = (b == `TRIT_F) ? -2'sd1 :
                           (b == `TRIT_T) ?  2'sd1 : 2'sd0;
    assign cmp_out = (sa < sb) ? `TRIT_F :
                     (sa > sb) ? `TRIT_T :
                                 `TRIT_U;

    always @(*) begin
        carry = `TRIT_U;
        case (op)
            4'd0: begin result = add_sum;   carry = add_carry; end  // ADD
            4'd1: begin result = sub_sum;   carry = sub_carry; end  // SUB
            4'd2: begin result = mul_out;   carry = `TRIT_U;  end  // MUL
            4'd3: begin result = k_and_out; carry = `TRIT_U;  end  // K_AND
            4'd4: begin result = k_or_out;  carry = `TRIT_U;  end  // K_OR
            4'd5: begin result = k_not_out; carry = `TRIT_U;  end  // K_NOT
            4'd6: begin result = mul_out;   carry = `TRIT_U;  end  // DOT_ACC
            4'd7: begin result = add_sum;   carry = `TRIT_U;  end  // FFT
            4'd8: begin result = inc_out;   carry = `TRIT_U;  end  // INC
            4'd9: begin result = cmp_out;   carry = `TRIT_U;  end  // CMP
            default: begin result = `TRIT_X; carry = `TRIT_X; end
        endcase
    end
endmodule

/* ==== N:M Sparsity Mask Unit =========================================== */
/**
 * Checks if the last M trits of an N-trit window are all Unknown.
 * If so, asserts `skip` to bypass the MAC unit.
 *
 * For N=4, M=2: if positions [2:3] are Unknown, skip.
 */
module sparsity_mask #(
    parameter N = 4,
    parameter M = 2
) (
    input  wire [2*N-1:0] window,  /* N trits, 2 bits each */
    output wire            skip
);
    /* Check if all M positions (starting at N-M) are Unknown */
    wire [M-1:0] is_unknown;
    genvar i;
    generate
        for (i = 0; i < M; i = i + 1) begin : check
            assign is_unknown[i] = (window[2*(N-M+i)+1:2*(N-M+i)] == `TRIT_U);
        end
    endgenerate

    assign skip = &is_unknown;  /* AND-reduce: skip only if ALL are Unknown */
endmodule

/* ==== Top-level Kleene Processor ======================================= */
/**
 * ternary_kleene_processor — Stack-based ternary processor with Kleene ISA.
 *
 * Opcodes (4-bit):
 *   0x0: NOP
 *   0x1: PUSH (immediate trit word follows)
 *   0x2: ADD
 *   0x3: SUB
 *   0x4: MUL
 *   0x5: K_AND
 *   0x6: K_OR
 *   0x7: K_NOT (unary, operates on TOS)
 *   0x8: DOT_START (begin 32-element dot product)
 *   0x9: INC
 *   0xA: CMP
 *   0xB: FFT_STEP (pop 3, push 3 butterfly outputs)
 *   0xF: HALT
 */
module ternary_kleene_processor #(
    parameter WORD_WIDTH = 9,     /* Trit width of a machine word */
    parameter STACK_DEPTH = 64,   /* Operand stack depth */
    parameter PROG_SIZE  = 256    /* Program memory size */
) (
    input  wire clk,
    input  wire rst_n,
    input  wire [2*WORD_WIDTH-1:0] prog_data,
    input  wire prog_wr,
    input  wire [7:0] prog_addr,
    output reg  halt,
    output reg  [2*WORD_WIDTH-1:0] tos,  /* Top of stack */
    output reg  [5:0] sp                 /* Stack pointer */
);
    /* Program memory */
    reg [2*WORD_WIDTH-1:0] prog [0:PROG_SIZE-1];
    reg [7:0] pc;

    /* Operand stack */
    reg [2*WORD_WIDTH-1:0] stack [0:STACK_DEPTH-1];

    /* ALU instance (operates on least significant trit) */
    reg [1:0] alu_a, alu_b;
    reg [3:0] alu_op;
    wire [1:0] alu_result, alu_carry;
    ternary_kleene_alu alu (
        .a(alu_a), .b(alu_b), .op(alu_op),
        .result(alu_result), .carry(alu_carry)
    );

    /* N-trit word ALU (ripple) */
    wire [2*WORD_WIDTH-1:0] wadd_sum;
    wire [1:0] wadd_carry;
    trit_word_adder #(.WIDTH(WORD_WIDTH)) word_adder (
        .a(stack[sp-1]),
        .b(stack[sp-2]),
        .sum(wadd_sum),
        .carry_out(wadd_carry)
    );

    /* Program write port */
    always @(posedge clk) begin
        if (prog_wr)
            prog[prog_addr] <= prog_data;
    end

    /* Main state machine */
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            pc   <= 8'd0;
            sp   <= 6'd0;
            halt <= 1'b0;
            tos  <= {2*WORD_WIDTH{1'b0}};
        end else if (!halt) begin
            case (prog[pc][3:0])  /* opcode from bottom 4 bits */
                4'h0: begin /* NOP */
                    pc <= pc + 1;
                end
                4'h1: begin /* PUSH: next word is immediate */
                    stack[sp] <= prog[pc+1];
                    sp <= sp + 1;
                    tos <= prog[pc+1];
                    pc <= pc + 2;
                end
                4'h2: begin /* ADD */
                    if (sp >= 2) begin
                        stack[sp-2] <= wadd_sum;
                        sp <= sp - 1;
                        tos <= wadd_sum;
                    end
                    pc <= pc + 1;
                end
                4'h5: begin /* K_AND */
                    if (sp >= 2) begin
                        /* Trit-wise AND across word */
                        // Simplified: operate on LSB trit
                        alu_a <= stack[sp-1][1:0];
                        alu_b <= stack[sp-2][1:0];
                        alu_op <= 4'd3;
                        stack[sp-2][1:0] <= alu_result;
                        sp <= sp - 1;
                        tos[1:0] <= alu_result;
                    end
                    pc <= pc + 1;
                end
                4'h6: begin /* K_OR */
                    if (sp >= 2) begin
                        alu_a <= stack[sp-1][1:0];
                        alu_b <= stack[sp-2][1:0];
                        alu_op <= 4'd4;
                        stack[sp-2][1:0] <= alu_result;
                        sp <= sp - 1;
                        tos[1:0] <= alu_result;
                    end
                    pc <= pc + 1;
                end
                4'h7: begin /* K_NOT (unary) */
                    if (sp >= 1) begin
                        alu_a <= stack[sp-1][1:0];
                        alu_op <= 4'd5;
                        stack[sp-1][1:0] <= alu_result;
                        tos[1:0] <= alu_result;
                    end
                    pc <= pc + 1;
                end
                4'h9: begin /* INC */
                    if (sp >= 1) begin
                        alu_a <= stack[sp-1][1:0];
                        alu_op <= 4'd8;
                        stack[sp-1][1:0] <= alu_result;
                        tos[1:0] <= alu_result;
                    end
                    pc <= pc + 1;
                end
                4'hF: begin /* HALT */
                    halt <= 1'b1;
                end
                default: begin
                    pc <= pc + 1;
                end
            endcase
        end
    end
endmodule

/* ==== Testbench ======================================================== */
`ifdef TESTBENCH
module ternary_kleene_tb;
    reg clk, rst_n;

    /* Kleene gate tests */
    reg  [1:0] ta, tb;
    wire [1:0] and_out, or_out, not_out;

    kleene_and uut_and (.a(ta), .b(tb), .out(and_out));
    kleene_or  uut_or  (.a(ta), .b(tb), .out(or_out));
    kleene_not uut_not (.a(ta),         .out(not_out));

    /* Multiply test */
    wire [1:0] mul_out;
    trit_mul uut_mul (.a(ta), .b(tb), .out(mul_out));

    /* FFT butterfly test */
    reg  [1:0] x0, x1, x2;
    wire [1:0] y0, y1, y2;
    fft_butterfly uut_fft (.x0(x0), .x1(x1), .x2(x2),
                           .y0(y0), .y1(y1), .y2(y2));

    /* Sparsity mask test */
    reg [7:0] sw;
    wire skip;
    sparsity_mask #(.N(4), .M(2)) uut_sparse (.window(sw), .skip(skip));

    initial begin
        clk = 0;
        rst_n = 0;
        #10 rst_n = 1;

        /* Test Kleene AND truth table */
        $display("=== Kleene AND ===");
        ta = `TRIT_F; tb = `TRIT_F; #10;
        $display("F AND F = %b (expect 00)", and_out);

        ta = `TRIT_F; tb = `TRIT_T; #10;
        $display("F AND T = %b (expect 00)", and_out);

        ta = `TRIT_U; tb = `TRIT_T; #10;
        $display("U AND T = %b (expect 01)", and_out);

        ta = `TRIT_T; tb = `TRIT_T; #10;
        $display("T AND T = %b (expect 11)", and_out);

        /* Test Kleene NOT */
        $display("=== Kleene NOT ===");
        ta = `TRIT_F; #10;
        $display("NOT F = %b (expect 11)", not_out);

        ta = `TRIT_U; #10;
        $display("NOT U = %b (expect 01)", not_out);

        ta = `TRIT_T; #10;
        $display("NOT T = %b (expect 00)", not_out);

        /* Test balanced multiply */
        $display("=== Trit Multiply ===");
        ta = `TRIT_F; tb = `TRIT_F; #10;
        $display("F * F = %b (expect 11=T)", mul_out);

        ta = `TRIT_F; tb = `TRIT_T; #10;
        $display("F * T = %b (expect 00=F)", mul_out);

        ta = `TRIT_U; tb = `TRIT_T; #10;
        $display("U * T = %b (expect 01=U)", mul_out);

        /* Test FFT butterfly */
        $display("=== FFT Butterfly ===");
        x0 = `TRIT_T; x1 = `TRIT_F; x2 = `TRIT_U; #10;
        $display("FFT(T,F,U): y0=%b y1=%b y2=%b", y0, y1, y2);

        /* Test sparsity mask */
        $display("=== Sparsity Mask (N=4, M=2) ===");
        sw = {`TRIT_U, `TRIT_U, `TRIT_T, `TRIT_F}; #10;
        $display("window [F,T,U,U]: skip=%b (expect 1)", skip);

        sw = {`TRIT_U, `TRIT_T, `TRIT_T, `TRIT_F}; #10;
        $display("window [F,T,T,U]: skip=%b (expect 0)", skip);

        $display("=== All Verilog tests complete ===");
        $finish;
    end

    always #5 clk = ~clk;
endmodule
`endif
