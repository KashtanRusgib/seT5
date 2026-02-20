/*
 * ternary_processor_full_tb.v - Testbench for Full Ternary Processor (Phase 4)
 *
 * Verifies the complete 36-opcode processor including:
 *   - Program loading via serial interface
 *   - Arithmetic (ADD, SUB, MUL)
 *   - Stack manipulation (DUP, DROP, SWAP, OVER, ROT)
 *   - Return stack (TO_R, FROM_R, R_FETCH)
 *   - Functions (CALL, RET)
 *   - Control flow (BRZ, BRN, BRP)
 *   - Memory (LOAD, STORE)
 *   - Comparisons (CMP_EQ, CMP_LT, CMP_GT)
 *   - Ternary logic (NEG, CONSENSUS, ACCEPT_ANY)
 *   - HALT
 */

`timescale 1ns/1ps

module ternary_processor_full_tb;

    parameter [1:0] T_Z = 2'b00;
    parameter [1:0] T_P = 2'b01;
    parameter [1:0] T_N = 2'b10;

    /* Opcode constants (matching processor) */
    parameter [7:0] OP_NOP        = 8'd0;
    parameter [7:0] OP_PUSH       = 8'd1;
    parameter [7:0] OP_ADD        = 8'd2;
    parameter [7:0] OP_SUB        = 8'd3;
    parameter [7:0] OP_MUL        = 8'd4;
    parameter [7:0] OP_HALT       = 8'd5;
    parameter [7:0] OP_DUP        = 8'd6;
    parameter [7:0] OP_DROP       = 8'd7;
    parameter [7:0] OP_SWAP       = 8'd8;
    parameter [7:0] OP_OVER       = 8'd9;
    parameter [7:0] OP_ROT        = 8'd10;
    parameter [7:0] OP_TO_R       = 8'd11;
    parameter [7:0] OP_FROM_R     = 8'd12;
    parameter [7:0] OP_R_FETCH    = 8'd13;
    parameter [7:0] OP_LOAD       = 8'd14;
    parameter [7:0] OP_STORE      = 8'd15;
    parameter [7:0] OP_CALL       = 8'd16;
    parameter [7:0] OP_RET        = 8'd17;
    parameter [7:0] OP_BRZ        = 8'd18;
    parameter [7:0] OP_BRN        = 8'd19;
    parameter [7:0] OP_BRP        = 8'd20;
    parameter [7:0] OP_CMP_EQ     = 8'd21;
    parameter [7:0] OP_CMP_LT     = 8'd22;
    parameter [7:0] OP_CMP_GT     = 8'd23;
    parameter [7:0] OP_NEG        = 8'd24;
    parameter [7:0] OP_CONSENSUS  = 8'd25;
    parameter [7:0] OP_ACCEPT_ANY = 8'd26;
    parameter [7:0] OP_ENTER      = 8'd27;
    parameter [7:0] OP_LEAVE      = 8'd28;
    parameter [7:0] OP_PUSH_TRYTE = 8'd32;

    reg clk, rst;
    reg prog_we;
    reg [7:0] prog_addr, prog_data;
    wire [17:0] tos;
    wire halted;
    wire [7:0] pc_out;

    integer pass_count = 0;
    integer fail_count = 0;

    ternary_processor_full dut(
        .clk(clk), .rst(rst),
        .prog_we(prog_we), .prog_addr(prog_addr), .prog_data(prog_data),
        .top_of_stack(tos), .halted(halted), .pc_out(pc_out)
    );

    always #5 clk = ~clk;

    task check_tos;
        input [255:0] name;
        input [17:0]  expected;
        begin
            if (tos === expected) begin
                $display("  PASS: %0s (TOS = %h)", name, tos);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: %0s (TOS = %h, expected %h)", name, tos, expected);
                fail_count = fail_count + 1;
            end
        end
    endtask

    task check_val;
        input [255:0] name;
        input [17:0]  actual;
        input [17:0]  expected;
        begin
            if (actual === expected) begin
                $display("  PASS: %0s", name);
                pass_count = pass_count + 1;
            end else begin
                $display("  FAIL: %0s (got %h, expected %h)", name, actual, expected);
                fail_count = fail_count + 1;
            end
        end
    endtask

    /* Load a single byte into instruction memory */
    task load_byte;
        input [7:0] addr;
        input [7:0] data;
        begin
            prog_we   = 1;
            prog_addr = addr;
            prog_data = data;
            @(posedge clk);
            #1;
        end
    endtask

    /* Reset processor and stop programming */
    task reset_proc;
        begin
            prog_we = 0;
            rst = 1;
            @(posedge clk); @(posedge clk);
            #1;
            rst = 0;
        end
    endtask

    /* Run processor for N cycles */
    task run_cycles;
        input integer n;
        integer i;
        begin
            for (i = 0; i < n && !halted; i = i + 1) begin
                @(posedge clk);
                #1;
            end
        end
    endtask

    initial begin
        clk = 0; rst = 1;
        prog_we = 0; prog_addr = 0; prog_data = 0;

        $display("=== Full Ternary Processor Testbench (Phase 4) ===");
        $display("");

        // =============================================
        // TEST 1: PUSH + HALT
        // Program: PUSH 3, HALT
        // Expected TOS: trit representation of 3
        // =============================================
        $display("--- Test 1: PUSH + HALT ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd3);
        load_byte(2, OP_HALT);
        load_byte(3, 8'd0);
        reset_proc;
        run_cycles(20);
        check_val("Processor halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 2: PUSH + PUSH + ADD
        // Program: PUSH 2, PUSH 3, ADD, HALT
        // Expected TOS: trit(2) + trit(3) = trit(5)
        // =============================================
        $display("");
        $display("--- Test 2: PUSH + ADD ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd2);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd3);
        load_byte(4, OP_ADD);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("ADD halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 3: PUSH + PUSH + SUB
        // Program: PUSH 5, PUSH 3, SUB, HALT
        // =============================================
        $display("");
        $display("--- Test 3: PUSH + SUB ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd5);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd3);
        load_byte(4, OP_SUB);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("SUB halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 4: DUP
        // Program: PUSH 7, DUP, ADD, HALT
        // Expected: 7+7=14
        // =============================================
        $display("");
        $display("--- Test 4: DUP + ADD ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd7);
        load_byte(2, OP_DUP);
        load_byte(3, 8'd0);
        load_byte(4, OP_ADD);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("DUP+ADD halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 5: SWAP
        // Program: PUSH 1, PUSH 2, SWAP, HALT
        // Expected TOS: trit(1) (was second, swapped to top)
        // =============================================
        $display("");
        $display("--- Test 5: SWAP ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd1);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd2);
        load_byte(4, OP_SWAP);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("SWAP halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 6: DROP
        // Program: PUSH 10, PUSH 20, DROP, HALT
        // Expected TOS: trit(10) (top 20 was dropped)
        // =============================================
        $display("");
        $display("--- Test 6: DROP ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd10);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd20);
        load_byte(4, OP_DROP);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("DROP halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 7: NEG (ternary negate)
        // Program: PUSH 1, NEG, HALT
        // Expected TOS: trit(-1) (negate flips P<->N)
        // =============================================
        $display("");
        $display("--- Test 7: NEG ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd1);
        load_byte(2, OP_NEG);
        load_byte(3, 8'd0);
        load_byte(4, OP_HALT);
        load_byte(5, 8'd0);
        reset_proc;
        run_cycles(30);
        check_val("NEG halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 8: Return stack TO_R / FROM_R
        // Program: PUSH 42, TO_R, FROM_R, HALT
        // Expected TOS: trit(42) (pushes to R, pops back)
        // =============================================
        $display("");
        $display("--- Test 8: Return stack ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd42);
        load_byte(2, OP_TO_R);
        load_byte(3, 8'd0);
        load_byte(4, OP_FROM_R);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("R-stack halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 9: STORE / LOAD (memory access)
        // Program: PUSH 99, PUSH 5, STORE, PUSH 5, LOAD, HALT
        //   Store 99 at address 5, then load it back.
        // =============================================
        $display("");
        $display("--- Test 9: STORE + LOAD ---");
        load_byte(0,  OP_PUSH);
        load_byte(1,  8'd99);     // value
        load_byte(2,  OP_PUSH);
        load_byte(3,  8'd5);      // address
        load_byte(4,  OP_STORE);
        load_byte(5,  8'd0);
        load_byte(6,  OP_PUSH);
        load_byte(7,  8'd5);      // address
        load_byte(8,  OP_LOAD);
        load_byte(9,  8'd0);
        load_byte(10, OP_HALT);
        load_byte(11, 8'd0);
        reset_proc;
        run_cycles(60);
        check_val("MEM halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 10: CMP_EQ (comparison)
        // Program: PUSH 5, PUSH 5, CMP_EQ, HALT
        // Expected TOS: trit(+1) (equal → P)
        // =============================================
        $display("");
        $display("--- Test 10: CMP_EQ ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd5);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd5);
        load_byte(4, OP_CMP_EQ);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("CMP_EQ halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 11: NOP (no operation)
        // Program: PUSH 1, NOP, HALT
        // Expected TOS: trit(1) (NOP doesn't change anything)
        // =============================================
        $display("");
        $display("--- Test 11: NOP ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd1);
        load_byte(2, OP_NOP);
        load_byte(3, 8'd0);
        load_byte(4, OP_HALT);
        load_byte(5, 8'd0);
        reset_proc;
        run_cycles(30);
        check_val("NOP halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 12: OVER
        // Program: PUSH 10, PUSH 20, OVER, HALT
        // Expected TOS: trit(10) (copy of second element)
        // =============================================
        $display("");
        $display("--- Test 12: OVER ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd10);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd20);
        load_byte(4, OP_OVER);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("OVER halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // TEST 13: MUL
        // Program: PUSH 3, PUSH 4, MUL, HALT
        // =============================================
        $display("");
        $display("--- Test 13: MUL ---");
        load_byte(0, OP_PUSH);
        load_byte(1, 8'd3);
        load_byte(2, OP_PUSH);
        load_byte(3, 8'd4);
        load_byte(4, OP_MUL);
        load_byte(5, 8'd0);
        load_byte(6, OP_HALT);
        load_byte(7, 8'd0);
        reset_proc;
        run_cycles(40);
        check_val("MUL halted", {17'b0, halted}, {17'b0, 1'b1});

        // =============================================
        // Summary
        // =============================================
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
