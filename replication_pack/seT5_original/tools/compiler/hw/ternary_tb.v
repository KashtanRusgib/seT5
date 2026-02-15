/*
 * ternary_tb.v - Testbench for Ternary ALU and Processor (TASK-017)
 *
 * Verifies: single-trit add/mul, 9-trit word add/sub,
 * ALU operations, and processor instruction execution.
 */

`timescale 1ns/1ps

module ternary_tb;

    // Trit constants
    parameter [1:0] T_Z = 2'b00;
    parameter [1:0] T_P = 2'b01;
    parameter [1:0] T_N = 2'b10;

    integer pass_count = 0;
    integer fail_count = 0;

    task check;
        input [255:0] test_name;
        input [17:0] actual;
        input [17:0] expected;
        begin
            if (actual === expected) begin
                $display("  PASS: %0s", test_name);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: %0s (got %b, expected %b)", test_name, actual, expected);
                fail_count = fail_count + 1;
            end
        end
    endtask

    // ---- Test single-trit adder ----
    reg [1:0] ta_a, ta_b, ta_cin;
    wire [1:0] ta_sum, ta_cout;

    trit_adder u_adder(
        .a(ta_a), .b(ta_b), .cin(ta_cin),
        .sum(ta_sum), .cout(ta_cout)
    );

    // ---- Test single-trit multiplier ----
    reg [1:0] tm_a, tm_b;
    wire [1:0] tm_product;

    trit_multiplier u_mul(
        .a(tm_a), .b(tm_b),
        .product(tm_product)
    );

    // ---- Test 9-trit word adder ----
    reg [17:0] wa_a, wa_b;
    wire [17:0] wa_sum;
    wire [1:0] wa_carry;

    trit_word_adder u_word_adder(
        .a(wa_a), .b(wa_b),
        .sum(wa_sum), .carry_out(wa_carry)
    );

    // ---- Test ALU ----
    reg [17:0] alu_a, alu_b;
    reg [1:0] alu_op;
    wire [17:0] alu_result;
    wire [1:0] alu_carry;

    ternary_alu u_alu(
        .a(alu_a), .b(alu_b),
        .op(alu_op), .result(alu_result),
        .carry(alu_carry)
    );

    // ---- Test processor ----
    reg clk, rst;
    reg [7:0] instr, operand;
    wire [17:0] tos;
    wire proc_halted;

    ternary_processor u_proc(
        .clk(clk), .rst(rst),
        .instruction(instr), .operand(operand),
        .top_of_stack(tos), .halted(proc_halted)
    );

    // Clock generation
    always #5 clk = ~clk;

    initial begin
        $display("=== Ternary Hardware Testbench (TASK-017) ===");
        $display("");

        // ---- Single-trit adder tests ----
        $display("--- Trit Adder ---");

        // P + N + Z = Z, carry Z
        ta_a = T_P; ta_b = T_N; ta_cin = T_Z; #1;
        check("P+N+Z=Z", {16'b0, ta_sum}, {16'b0, T_Z});

        // P + P + Z = N, carry P (sum=2, result=-1+3=2? no: sum=2>1, result=2-3=-1=N, carry=P)
        ta_a = T_P; ta_b = T_P; ta_cin = T_Z; #1;
        check("P+P+Z: sum=N", {16'b0, ta_sum}, {16'b0, T_N});
        check("P+P+Z: carry=P", {16'b0, ta_cout}, {16'b0, T_P});

        // N + N + Z = P, carry N (sum=-2<-1, result=-2+3=1=P, carry=N)
        ta_a = T_N; ta_b = T_N; ta_cin = T_Z; #1;
        check("N+N+Z: sum=P", {16'b0, ta_sum}, {16'b0, T_P});
        check("N+N+Z: carry=N", {16'b0, ta_cout}, {16'b0, T_N});

        // Z + Z + Z = Z
        ta_a = T_Z; ta_b = T_Z; ta_cin = T_Z; #1;
        check("Z+Z+Z=Z", {16'b0, ta_sum}, {16'b0, T_Z});

        // ---- Single-trit multiplier tests ----
        $display("");
        $display("--- Trit Multiplier ---");

        tm_a = T_P; tm_b = T_P; #1;
        check("P*P=P", {16'b0, tm_product}, {16'b0, T_P});

        tm_a = T_P; tm_b = T_N; #1;
        check("P*N=N", {16'b0, tm_product}, {16'b0, T_N});

        tm_a = T_N; tm_b = T_N; #1;
        check("N*N=P", {16'b0, tm_product}, {16'b0, T_P});

        tm_a = T_Z; tm_b = T_P; #1;
        check("Z*P=Z", {16'b0, tm_product}, {16'b0, T_Z});

        // ---- Word adder tests ----
        $display("");
        $display("--- Word Adder ---");

        // 1 + 1 = -1 with carry (in trit: P + P = N,carry=P -> balanced ternary for 2)
        // Represent 1 as: trit[0]=P, rest=Z -> 18'b00_00_00_00_00_00_00_00_01
        wa_a = 18'b00_00_00_00_00_00_00_00_01; // +1
        wa_b = 18'b00_00_00_00_00_00_00_00_01; // +1
        #1;
        // Expected: 2 in balanced ternary = [N,P] = trit[0]=N, trit[1]=P
        // 18'b00_00_00_00_00_00_00_01_10
        check("1+1=2 (balanced)", wa_sum, 18'b00_00_00_00_00_00_00_01_10);

        // ---- ALU tests ----
        $display("");
        $display("--- ALU ---");

        // ADD
        alu_a = 18'b00_00_00_00_00_00_00_00_01; // 1
        alu_b = 18'b00_00_00_00_00_00_00_00_01; // 1
        alu_op = 2'b00; #1;
        check("ALU ADD 1+1=2", alu_result, 18'b00_00_00_00_00_00_00_01_10);

        // SUB: 1 - 1 = 0
        alu_a = 18'b00_00_00_00_00_00_00_00_01;
        alu_b = 18'b00_00_00_00_00_00_00_00_01;
        alu_op = 2'b01; #1;
        check("ALU SUB 1-1=0", alu_result, 18'b00_00_00_00_00_00_00_00_00);

        // MUL (trit-wise): P * N = N
        alu_a = 18'b00_00_00_00_00_00_00_00_01; // trit[0]=P
        alu_b = 18'b00_00_00_00_00_00_00_00_10; // trit[0]=N
        alu_op = 2'b10; #1;
        check("ALU MUL P*N=N", alu_result, 18'b00_00_00_00_00_00_00_00_10);

        // ---- Processor tests ----
        $display("");
        $display("--- Processor ---");

        clk = 0; rst = 1;
        instr = 0; operand = 0;
        #10; rst = 0;

        // PUSH 1
        instr = 8'd0; operand = 8'd1;
        @(posedge clk); #1;

        // PUSH 2
        instr = 8'd0; operand = 8'd2;
        @(posedge clk); #1;

        // HALT
        instr = 8'd5; operand = 8'd0;
        @(posedge clk); #1;
        @(posedge clk); #1; // extra cycle for halt to register

        check("Proc halted", {17'b0, proc_halted}, {17'b0, 1'b1});

        // ---- Summary ----
        $display("");
        $display("========================================");
        $display("  %0d passed, %0d failed", pass_count, fail_count);
        $display("========================================");

        if (fail_count > 0)
            $finish(1);
        else
            $finish(0);
    end

endmodule
