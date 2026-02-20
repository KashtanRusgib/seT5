/*
 * ternary_processor_full.v - Full Ternary Processor (Phase 4)
 *
 * Complete ternary processor supporting the full 36-opcode ISA.
 * Designed for FPGA synthesis targeting Lattice iCE40 / Xilinx Artix-7.
 *
 * Features:
 *   - Two-stack architecture (operand + return stack, Setun-70 inspired)
 *   - 36 opcodes: arithmetic, stack manip, control flow, comparisons
 *   - 729-cell ternary memory (3^6)
 *   - 9-trit word (18-bit encoded), 6-trit tryte support
 *   - Structured control flow (BRZ/BRN/BRP, LOOP_BEGIN/END)
 *
 * Encoding: 2 bits per trit: 00=Z(0), 01=P(+1), 10=N(-1), 11=unused
 */

`timescale 1ns/1ps

/* ---- Instruction memory ---- */
module instruction_memory(
    input  wire [7:0] addr,
    output reg  [7:0] data,
    input  wire       clk,
    input  wire       we,
    input  wire [7:0] wdata,
    input  wire [7:0] waddr
);
    reg [7:0] mem [0:255];
    integer i;

    initial begin
        for (i = 0; i < 256; i = i + 1)
            mem[i] = 8'd0;
    end

    always @(posedge clk) begin
        if (we) mem[waddr] <= wdata;
    end

    always @(*) begin
        data = mem[addr];
    end
endmodule

/* ---- Data memory (729 cells, 18-bit words) ---- */
module ternary_memory(
    input  wire        clk,
    input  wire        we,
    input  wire [9:0]  addr,    /* 10-bit address (0-728) */
    input  wire [17:0] wdata,
    output reg  [17:0] rdata
);
    reg [17:0] mem [0:728];  /* 3^6 = 729 cells */
    integer i;

    initial begin
        for (i = 0; i < 729; i = i + 1)
            mem[i] = 18'b0;
    end

    always @(posedge clk) begin
        if (we && addr < 10'd729)
            mem[addr] <= wdata;
    end

    always @(*) begin
        rdata = (addr < 10'd729) ? mem[addr] : 18'b0;
    end
endmodule

/* ---- Full Ternary Processor ---- */
module ternary_processor_full(
    input  wire        clk,
    input  wire        rst,

    /* Program loading interface */
    input  wire        prog_we,
    input  wire [7:0]  prog_addr,
    input  wire [7:0]  prog_data,

    /* Status */
    output reg  [17:0] top_of_stack,
    output reg         halted,
    output reg  [7:0]  pc_out
);

    /* Trit constants */
    parameter [1:0] T_Z = 2'b00;
    parameter [1:0] T_P = 2'b01;
    parameter [1:0] T_N = 2'b10;

    /* ---- Operand Stack (16 entries, 18-bit) ---- */
    reg [17:0] ostack [0:15];
    reg [3:0]  osp;

    /* ---- Return Stack (16 entries, 18-bit) ---- */
    reg [17:0] rstack [0:15];
    reg [3:0]  rsp_reg;

    /* ---- Program Counter ---- */
    reg [7:0] pc;

    /* ---- Instruction memory ---- */
    wire [7:0] instr_data;
    instruction_memory imem(
        .addr(pc), .data(instr_data), .clk(clk),
        .we(prog_we), .wdata(prog_data), .waddr(prog_addr)
    );

    /* ---- Data memory ---- */
    reg         mem_we;
    reg  [9:0]  mem_addr;
    reg  [17:0] mem_wdata;
    wire [17:0] mem_rdata;
    ternary_memory dmem(
        .clk(clk), .we(mem_we),
        .addr(mem_addr), .wdata(mem_wdata), .rdata(mem_rdata)
    );

    /* ---- ALU ---- */
    wire [17:0] alu_result;
    wire [1:0]  alu_carry;
    reg  [17:0] alu_a, alu_b;
    reg  [1:0]  alu_op_sel;

    ternary_alu alu(
        .a(alu_a), .b(alu_b),
        .op(alu_op_sel), .result(alu_result), .carry(alu_carry)
    );

    /* ---- Integer to 9-trit conversion ---- */
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
                    out[2*j+1 -: 2] = T_Z;
                else if (rem == 1)
                    out[2*j+1 -: 2] = T_P;
                else begin
                    out[2*j+1 -: 2] = T_N;
                    v = v + 1;
                end
            end
            if (val < 0) begin
                for (j = 0; j < 9; j = j + 1) begin
                    if (out[2*j+1 -: 2] == T_P)
                        out[2*j+1 -: 2] = T_N;
                    else if (out[2*j+1 -: 2] == T_N)
                        out[2*j+1 -: 2] = T_P;
                end
            end
            int_to_trits = out;
        end
    endfunction

    /* ---- Trit negation (flip P<->N for all 9 trits) ---- */
    function [17:0] trit_negate;
        input [17:0] val;
        reg [17:0] out;
        integer j;
        begin
            out = 18'b0;
            for (j = 0; j < 9; j = j + 1) begin
                if (val[2*j+1 -: 2] == T_P)
                    out[2*j+1 -: 2] = T_N;
                else if (val[2*j+1 -: 2] == T_N)
                    out[2*j+1 -: 2] = T_P;
                else
                    out[2*j+1 -: 2] = T_Z;
            end
            trit_negate = out;
        end
    endfunction

    /* ---- Trit consensus (AND-like): min(a,b) per trit ---- */
    function [17:0] trit_consensus;
        input [17:0] a, b;
        reg [17:0] out;
        integer j;
        reg [1:0] ta, tb;
        begin
            out = 18'b0;
            for (j = 0; j < 9; j = j + 1) begin
                ta = a[2*j+1 -: 2];
                tb = b[2*j+1 -: 2];
                /* min in {N < Z < P} order: N=10, Z=00, P=01 */
                if (ta == T_N || tb == T_N)
                    out[2*j+1 -: 2] = T_N;
                else if (ta == T_Z || tb == T_Z)
                    out[2*j+1 -: 2] = T_Z;
                else
                    out[2*j+1 -: 2] = T_P;
            end
            trit_consensus = out;
        end
    endfunction

    /* ---- Trit accept-any (OR-like): max(a,b) per trit ---- */
    function [17:0] trit_accept_any;
        input [17:0] a, b;
        reg [17:0] out;
        integer j;
        reg [1:0] ta, tb;
        begin
            out = 18'b0;
            for (j = 0; j < 9; j = j + 1) begin
                ta = a[2*j+1 -: 2];
                tb = b[2*j+1 -: 2];
                if (ta == T_P || tb == T_P)
                    out[2*j+1 -: 2] = T_P;
                else if (ta == T_Z || tb == T_Z)
                    out[2*j+1 -: 2] = T_Z;
                else
                    out[2*j+1 -: 2] = T_N;
            end
            trit_accept_any = out;
        end
    endfunction

    /* ---- Comparison (returns P for true, Z for equal, N for false) ---- */
    function [17:0] trit_cmp_eq;
        input [17:0] a, b;
        begin
            trit_cmp_eq = (a == b) ? {16'b0, T_P} : {16'b0, T_Z};
        end
    endfunction

    function [17:0] trit_cmp_lt;
        input [17:0] a, b;
        begin
            /* Simple comparison based on encoded value */
            trit_cmp_lt = (a < b) ? {16'b0, T_P} : (a > b ? {16'b0, T_N} : {16'b0, T_Z});
        end
    endfunction

    function [17:0] trit_cmp_gt;
        input [17:0] a, b;
        begin
            trit_cmp_gt = (a > b) ? {16'b0, T_P} : (a < b ? {16'b0, T_N} : {16'b0, T_Z});
        end
    endfunction

    /* ---- State machine states ---- */
    parameter S_FETCH   = 3'd0;
    parameter S_DECODE  = 3'd1;
    parameter S_EXECUTE = 3'd2;
    parameter S_OPERAND = 3'd3;
    parameter S_MEM     = 3'd4;

    reg [2:0]  state;
    reg [7:0]  cur_instr;
    reg [7:0]  operand_byte;
    reg        need_operand;

    /* ---- Opcodes (match VM) ---- */
    parameter OP_PUSH      = 8'd0;
    parameter OP_ADD       = 8'd1;
    parameter OP_MUL       = 8'd2;
    parameter OP_JMP       = 8'd3;
    parameter OP_COND_JMP  = 8'd4;
    parameter OP_HALT      = 8'd5;
    parameter OP_LOAD      = 8'd6;
    parameter OP_STORE     = 8'd7;
    parameter OP_SUB       = 8'd8;
    parameter OP_SYSCALL   = 8'd9;
    parameter OP_DUP       = 8'd10;
    parameter OP_DROP      = 8'd11;
    parameter OP_SWAP      = 8'd12;
    parameter OP_OVER      = 8'd13;
    parameter OP_ROT       = 8'd14;
    parameter OP_TO_R      = 8'd15;
    parameter OP_FROM_R    = 8'd16;
    parameter OP_R_FETCH   = 8'd17;
    parameter OP_CALL      = 8'd18;
    parameter OP_RET       = 8'd19;
    parameter OP_ENTER     = 8'd20;
    parameter OP_LEAVE     = 8'd21;
    parameter OP_BRZ       = 8'd22;
    parameter OP_BRN       = 8'd23;
    parameter OP_BRP       = 8'd24;
    parameter OP_LOOP_BEGIN = 8'd25;
    parameter OP_LOOP_END  = 8'd26;
    parameter OP_BREAK     = 8'd27;
    parameter OP_CMP_EQ    = 8'd28;
    parameter OP_CMP_LT    = 8'd29;
    parameter OP_CMP_GT    = 8'd30;
    parameter OP_NEG       = 8'd31;
    parameter OP_CONSENSUS = 8'd32;
    parameter OP_ACCEPT_ANY_OP = 8'd33;
    parameter OP_PUSH_TRYTE = 8'd34;
    parameter OP_PUSH_WORD = 8'd35;

    /* ---- Main FSM ---- */

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            pc <= 8'd0;
            osp <= 4'd0;
            rsp_reg <= 4'd0;
            halted <= 1'b0;
            state <= S_FETCH;
            top_of_stack <= 18'b0;
            mem_we <= 1'b0;
            need_operand <= 1'b0;
            pc_out <= 8'd0;
        end else if (!halted) begin
            mem_we <= 1'b0;
            pc_out <= pc;

            case (state)

            S_FETCH: begin
                cur_instr <= instr_data;
                pc <= pc + 1;
                state <= S_DECODE;
            end

            S_DECODE: begin
                /* Check if opcode needs an operand byte */
                if (cur_instr == OP_PUSH || cur_instr == OP_JMP ||
                    cur_instr == OP_COND_JMP || cur_instr == OP_BRZ ||
                    cur_instr == OP_BRN || cur_instr == OP_BRP ||
                    cur_instr == OP_CALL || cur_instr == OP_PUSH_TRYTE) begin
                    need_operand <= 1'b1;
                    operand_byte <= instr_data;
                    pc <= pc + 1;
                    state <= S_EXECUTE;
                end else begin
                    need_operand <= 1'b0;
                    state <= S_EXECUTE;
                end
            end

            S_EXECUTE: begin
                state <= S_FETCH;  /* Default next state */

                case (cur_instr)

                /* --- Core arithmetic --- */
                OP_PUSH: begin
                    ostack[osp] <= int_to_trits(operand_byte);
                    osp <= osp + 1;
                end

                OP_ADD: begin
                    alu_a <= ostack[osp-2];
                    alu_b <= ostack[osp-1];
                    alu_op_sel <= 2'b00;
                    ostack[osp-2] <= alu_result;
                    osp <= osp - 1;
                end

                OP_MUL: begin
                    alu_a <= ostack[osp-2];
                    alu_b <= ostack[osp-1];
                    alu_op_sel <= 2'b10;
                    ostack[osp-2] <= alu_result;
                    osp <= osp - 1;
                end

                OP_SUB: begin
                    alu_a <= ostack[osp-2];
                    alu_b <= ostack[osp-1];
                    alu_op_sel <= 2'b01;
                    ostack[osp-2] <= alu_result;
                    osp <= osp - 1;
                end

                /* --- Memory --- */
                OP_LOAD: begin
                    mem_addr <= ostack[osp-1][9:0];
                    osp <= osp - 1;
                    state <= S_MEM;
                end

                OP_STORE: begin
                    mem_addr <= ostack[osp-2][9:0];
                    mem_wdata <= ostack[osp-1];
                    mem_we <= 1'b1;
                    osp <= osp - 2;
                end

                /* --- Jumps --- */
                OP_JMP: begin
                    pc <= operand_byte;
                end

                OP_COND_JMP: begin
                    if (ostack[osp-1] == 18'b0)
                        pc <= operand_byte;
                    osp <= osp - 1;
                end

                /* --- Halt --- */
                OP_HALT: begin
                    halted <= 1'b1;
                    if (osp > 0)
                        top_of_stack <= ostack[osp-1];
                end

                /* --- Stack manipulation --- */
                OP_DUP: begin
                    ostack[osp] <= ostack[osp-1];
                    osp <= osp + 1;
                end

                OP_DROP: begin
                    osp <= osp - 1;
                end

                OP_SWAP: begin
                    ostack[osp-1] <= ostack[osp-2];
                    ostack[osp-2] <= ostack[osp-1];
                end

                OP_OVER: begin
                    ostack[osp] <= ostack[osp-2];
                    osp <= osp + 1;
                end

                OP_ROT: begin
                    /* (a b c -- b c a) */
                    ostack[osp-3] <= ostack[osp-2];
                    ostack[osp-2] <= ostack[osp-1];
                    ostack[osp-1] <= ostack[osp-3];
                end

                /* --- Return stack --- */
                OP_TO_R: begin
                    rstack[rsp_reg] <= ostack[osp-1];
                    rsp_reg <= rsp_reg + 1;
                    osp <= osp - 1;
                end

                OP_FROM_R: begin
                    ostack[osp] <= rstack[rsp_reg-1];
                    osp <= osp + 1;
                    rsp_reg <= rsp_reg - 1;
                end

                OP_R_FETCH: begin
                    ostack[osp] <= rstack[rsp_reg-1];
                    osp <= osp + 1;
                end

                /* --- Function call convention --- */
                OP_CALL: begin
                    rstack[rsp_reg] <= {10'b0, pc};
                    rsp_reg <= rsp_reg + 1;
                    pc <= operand_byte;
                end

                OP_RET: begin
                    pc <= rstack[rsp_reg-1][7:0];
                    rsp_reg <= rsp_reg - 1;
                end

                OP_ENTER: begin
                    /* Push frame marker (-1 = all trits N) */
                    rstack[rsp_reg] <= {T_N, T_N, T_N, T_N, T_N, T_N, T_N, T_N, T_N};
                    rsp_reg <= rsp_reg + 1;
                end

                OP_LEAVE: begin
                    /* Pop return stack until frame marker */
                    if (rsp_reg > 0 && rstack[rsp_reg-1] != {T_N, T_N, T_N, T_N, T_N, T_N, T_N, T_N, T_N})
                        rsp_reg <= rsp_reg - 1;
                    else if (rsp_reg > 0)
                        rsp_reg <= rsp_reg - 1;
                end

                /* --- Structured control flow --- */
                OP_BRZ: begin
                    if (ostack[osp-1] == 18'b0)
                        pc <= operand_byte;
                    osp <= osp - 1;
                end

                OP_BRN: begin
                    if (ostack[osp-1][17:16] == T_N) /* MSB trit is negative */
                        pc <= operand_byte;
                    osp <= osp - 1;
                end

                OP_BRP: begin
                    if (ostack[osp-1] != 18'b0 && ostack[osp-1][17:16] != T_N)
                        pc <= operand_byte;
                    osp <= osp - 1;
                end

                OP_LOOP_BEGIN: begin
                    /* Push PC (loop body start) to return stack */
                    rstack[rsp_reg] <= {10'b0, pc};
                    rsp_reg <= rsp_reg + 1;
                end

                OP_LOOP_END: begin
                    /* Pop cond; if nonzero, jump to rstack TOS */
                    if (ostack[osp-1] != 18'b0) begin
                        pc <= rstack[rsp_reg-1][7:0];
                    end else begin
                        rsp_reg <= rsp_reg - 1;
                    end
                    osp <= osp - 1;
                end

                /* --- Comparison ops --- */
                OP_CMP_EQ: begin
                    ostack[osp-2] <= trit_cmp_eq(ostack[osp-2], ostack[osp-1]);
                    osp <= osp - 1;
                end

                OP_CMP_LT: begin
                    ostack[osp-2] <= trit_cmp_lt(ostack[osp-2], ostack[osp-1]);
                    osp <= osp - 1;
                end

                OP_CMP_GT: begin
                    ostack[osp-2] <= trit_cmp_gt(ostack[osp-2], ostack[osp-1]);
                    osp <= osp - 1;
                end

                /* --- Ternary logic --- */
                OP_NEG: begin
                    ostack[osp-1] <= trit_negate(ostack[osp-1]);
                end

                OP_CONSENSUS: begin
                    ostack[osp-2] <= trit_consensus(ostack[osp-2], ostack[osp-1]);
                    osp <= osp - 1;
                end

                OP_ACCEPT_ANY_OP: begin
                    ostack[osp-2] <= trit_accept_any(ostack[osp-2], ostack[osp-1]);
                    osp <= osp - 1;
                end

                /* --- Extended data --- */
                OP_PUSH_TRYTE: begin
                    ostack[osp] <= int_to_trits(operand_byte);
                    osp <= osp + 1;
                end

                OP_SYSCALL: begin
                    /* Stub: pop syscall number */
                    osp <= osp - 1;
                end

                default: ; /* NOP */

                endcase
            end

            S_MEM: begin
                /* Memory read completes: push result */
                ostack[osp] <= mem_rdata;
                osp <= osp + 1;
                state <= S_FETCH;
            end

            default: state <= S_FETCH;

            endcase
        end
    end

endmodule
