/*
 * ternary_alu.v - Ternary ALU in Verilog (TASK-017)
 *
 * 2-bit encoding for each trit:
 *   2'b00 = Z (zero)
 *   2'b01 = P (+1)
 *   2'b10 = N (-1)
 *   2'b11 = invalid (unused)
 *
 * A 9-trit word = 18 bits.
 * ALU operations: ADD, MUL, SUB, MIN, MAX
 */

module trit_encode;
    // Constants for trit encoding
    parameter [1:0] T_Z = 2'b00;  // Zero
    parameter [1:0] T_P = 2'b01;  // Positive (+1)
    parameter [1:0] T_N = 2'b10;  // Negative (-1)
endmodule

/*
 * Single-trit adder with carry
 * Inputs: a[1:0], b[1:0], cin[1:0]
 * Outputs: sum[1:0], cout[1:0]
 */
module trit_adder(
    input  [1:0] a,
    input  [1:0] b,
    input  [1:0] cin,
    output reg [1:0] sum,
    output reg [1:0] cout
);
    // Convert trit encoding to signed integer (-1, 0, +1)
    function signed [2:0] trit_to_int;
        input [1:0] t;
        begin
            case (t)
                2'b00: trit_to_int = 0;
                2'b01: trit_to_int = 1;
                2'b10: trit_to_int = -1;
                default: trit_to_int = 0;
            endcase
        end
    endfunction

    // Convert signed integer back to trit encoding
    function [1:0] int_to_trit;
        input signed [2:0] v;
        begin
            case (v)
                0:  int_to_trit = 2'b00;
                1:  int_to_trit = 2'b01;
                -1: int_to_trit = 2'b10;
                default: int_to_trit = 2'b00;
            endcase
        end
    endfunction

    reg signed [2:0] s;

    always @(*) begin
        s = trit_to_int(a) + trit_to_int(b) + trit_to_int(cin);
        if (s > 1) begin
            sum = int_to_trit(s - 3);
            cout = 2'b01; // carry = P
        end else if (s < -1) begin
            sum = int_to_trit(s + 3);
            cout = 2'b10; // carry = N
        end else begin
            sum = int_to_trit(s);
            cout = 2'b00; // carry = Z
        end
    end
endmodule

/*
 * Single-trit multiplier
 * trit_mul(a, b) = a * b
 */
module trit_multiplier(
    input  [1:0] a,
    input  [1:0] b,
    output reg [1:0] product
);
    always @(*) begin
        case ({a, b})
            {2'b01, 2'b01}: product = 2'b01; // P*P = P
            {2'b01, 2'b10}: product = 2'b10; // P*N = N
            {2'b10, 2'b01}: product = 2'b10; // N*P = N
            {2'b10, 2'b10}: product = 2'b01; // N*N = P
            default:         product = 2'b00; // anything * Z = Z
        endcase
    end
endmodule

/*
 * 9-trit word adder (ripple carry)
 * 18-bit inputs/outputs (9 trits × 2 bits each)
 */
module trit_word_adder(
    input  [17:0] a,
    input  [17:0] b,
    output [17:0] sum,
    output [1:0]  carry_out
);
    wire [1:0] carry [0:9];
    assign carry[0] = 2'b00; // initial carry = Z

    genvar i;
    generate
        for (i = 0; i < 9; i = i + 1) begin : adder_chain
            trit_adder ta(
                .a(a[2*i+1 : 2*i]),
                .b(b[2*i+1 : 2*i]),
                .cin(carry[i]),
                .sum(sum[2*i+1 : 2*i]),
                .cout(carry[i+1])
            );
        end
    endgenerate

    assign carry_out = carry[9];
endmodule

/*
 * Ternary ALU - supports ADD, SUB, MUL (trit-by-trit for mul)
 * op: 2'b00 = ADD, 2'b01 = SUB, 2'b10 = MUL
 */
module ternary_alu(
    input  [17:0] a,
    input  [17:0] b,
    input  [1:0]  op,
    output reg [17:0] result,
    output [1:0] carry
);
    // ADD result
    wire [17:0] add_result;
    wire [1:0] add_carry;
    trit_word_adder adder(
        .a(a), .b(b),
        .sum(add_result), .carry_out(add_carry)
    );

    // Negate b for SUB (flip P<->N)
    wire [17:0] b_neg;
    genvar i;
    generate
        for (i = 0; i < 9; i = i + 1) begin : negate
            assign b_neg[2*i+1 : 2*i] =
                (b[2*i+1 : 2*i] == 2'b01) ? 2'b10 :
                (b[2*i+1 : 2*i] == 2'b10) ? 2'b01 :
                2'b00;
        end
    endgenerate

    wire [17:0] sub_result;
    wire [1:0] sub_carry;
    trit_word_adder subtractor(
        .a(a), .b(b_neg),
        .sum(sub_result), .carry_out(sub_carry)
    );

    // MUL: trit-by-trit (element-wise, not full multiply)
    // Full schoolbook multiply would need shift-and-add
    wire [17:0] mul_result;
    generate
        for (i = 0; i < 9; i = i + 1) begin : mul_trits
            trit_multiplier tm(
                .a(a[2*i+1 : 2*i]),
                .b(b[2*i+1 : 2*i]),
                .product(mul_result[2*i+1 : 2*i])
            );
        end
    endgenerate

    assign carry = (op == 2'b00) ? add_carry :
                   (op == 2'b01) ? sub_carry : 2'b00;

    always @(*) begin
        case (op)
            2'b00: result = add_result;
            2'b01: result = sub_result;
            2'b10: result = mul_result;
            default: result = 18'b0;
        endcase
    end
endmodule

/*
 * Simple ternary processor - fetches and executes bytecode
 * Opcodes match the VM: PUSH=0, ADD=1, MUL=2, HALT=5
 */
module ternary_processor(
    input wire clk,
    input wire rst,
    input wire [7:0] instruction,
    input wire [7:0] operand,
    output reg [17:0] top_of_stack,
    output reg halted
);
    // Stack: 16 entries of 18-bit ternary words
    reg [17:0] stack [0:15];
    reg [3:0] sp;

    // ALU interface
    reg [17:0] alu_a, alu_b;
    reg [1:0] alu_op;
    wire [17:0] alu_result;
    wire [1:0] alu_carry;

    ternary_alu alu(
        .a(alu_a), .b(alu_b),
        .op(alu_op), .result(alu_result),
        .carry(alu_carry)
    );

    // Integer to 9-trit conversion (simplified for small values)
    function [17:0] int_to_trits;
        input signed [7:0] val;
        reg signed [7:0] v;
        reg [17:0] out;
        integer j;
        reg [2:0] rem;
        begin
            out = 18'b0;
            v = (val < 0) ? -val : val;
            for (j = 0; j < 9 && v > 0; j = j + 1) begin
                rem = v % 3;
                v = v / 3;
                if (rem == 0)
                    out[2*j+1 -: 2] = 2'b00;
                else if (rem == 1)
                    out[2*j+1 -: 2] = 2'b01;
                else begin
                    out[2*j+1 -: 2] = 2'b10;
                    v = v + 1;
                end
            end
            if (val < 0) begin
                for (j = 0; j < 9; j = j + 1) begin
                    if (out[2*j+1 -: 2] == 2'b01)
                        out[2*j+1 -: 2] = 2'b10;
                    else if (out[2*j+1 -: 2] == 2'b10)
                        out[2*j+1 -: 2] = 2'b01;
                end
            end
            int_to_trits = out;
        end
    endfunction

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            sp <= 0;
            halted <= 0;
            top_of_stack <= 18'b0;
        end else if (!halted) begin
            case (instruction)
                8'd0: begin // OP_PUSH
                    stack[sp] <= int_to_trits(operand);
                    sp <= sp + 1;
                end
                8'd1: begin // OP_ADD
                    alu_a <= stack[sp-2];
                    alu_b <= stack[sp-1];
                    alu_op <= 2'b00;
                    stack[sp-2] <= alu_result;
                    sp <= sp - 1;
                end
                8'd2: begin // OP_MUL
                    alu_a <= stack[sp-2];
                    alu_b <= stack[sp-1];
                    alu_op <= 2'b10;
                    stack[sp-2] <= alu_result;
                    sp <= sp - 1;
                end
                8'd5: begin // OP_HALT
                    halted <= 1;
                    if (sp > 0)
                        top_of_stack <= stack[sp-1];
                end
                default: ; // NOP
            endcase
        end
    end
endmodule
