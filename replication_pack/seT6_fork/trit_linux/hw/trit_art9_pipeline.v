/**
 * @file trit_art9_pipeline.v
 * @brief seT6 ART-9 Ternary Pipeline — Verilog RTL Prototype
 *
 * 5-stage RISC ternary pipeline inspired by ART-9 (arXiv:2111.07584v1).
 * Uses 2-bit encoding for balanced ternary: 2'b00 = 0, 2'b01 = +1, 2'b10 = -1
 * Each 9-trit word = 18 bits in 2-bit encoded form.
 *
 * Stages: IF → ID → EX → MEM → WB
 * RAW hazard detection with 1-cycle stall.
 * 9 GPTRs (2-trit index), 24-instruction ISA.
 *
 * Target: CNTFET at 3.06×10⁶ DMIPS/W (theoretical)
 *         FPGA at 57.8 DMIPS/W (measured)
 *
 * SPDX-License-Identifier: GPL-2.0
 */

/* ======================================================================== */
/*  Balanced Ternary Encoding (2-bit per trit state)                       */
/* ======================================================================== */
`define TRIT_ZERO  2'b00
`define TRIT_POS   2'b01
`define TRIT_NEG   2'b10
`define TRIT_UNDEF 2'b11   // Unused / invalid

`define TRIT_WIDTH 2
`define WORD_TRITS 9
`define WORD_BITS  (`TRIT_WIDTH * `WORD_TRITS)  // 18 bits

/* Register file: 9 GPTRs (ART-9 paper specifies 9, indexed by 2 trits) */
`define NUM_REGS   9
`define REG_BITS   4       // ceil(log2(9))

/* Opcodes (4-bit field for 24 instructions) */
`define OP_TADD    4'd0
`define OP_TSUB    4'd1
`define OP_TMUL    4'd2
`define OP_TNEG    4'd3
`define OP_TAND    4'd4     // Kleene min(a,b)
`define OP_TOR     4'd5     // Kleene max(a,b)
`define OP_TMIN    4'd6
`define OP_TMAX    4'd7
`define OP_TSHL    4'd8
`define OP_TSHR    4'd9
`define OP_TCMP    4'd10
`define OP_TLOAD   4'd11
`define OP_TSTORE  4'd12
`define OP_TNOP    4'd13
`define OP_THALT   4'd14
`define OP_TMOVI   4'd15    // Move immediate

/* ======================================================================== */
/*  Balanced Ternary Full Adder (per-trit)                                 */
/* ======================================================================== */
module trit_full_adder(
    input  [`TRIT_WIDTH-1:0] a,
    input  [`TRIT_WIDTH-1:0] b,
    input  [`TRIT_WIDTH-1:0] cin,
    output reg [`TRIT_WIDTH-1:0] sum,
    output reg [`TRIT_WIDTH-1:0] cout
);
    /* Convert 2-bit encoding to signed: 00→0, 01→+1, 10→-1 */
    function signed [1:0] trit_to_signed;
        input [`TRIT_WIDTH-1:0] t;
        case(t)
            `TRIT_ZERO: trit_to_signed = 2'sb00;
            `TRIT_POS:  trit_to_signed = 2'sb01;
            `TRIT_NEG:  trit_to_signed = -2'sb01;
            default:    trit_to_signed = 2'sb00;
        endcase
    endfunction

    function [`TRIT_WIDTH-1:0] signed_to_trit;
        input signed [2:0] v;
        case(v)
             0: signed_to_trit = `TRIT_ZERO;
             1: signed_to_trit = `TRIT_POS;
            -1: signed_to_trit = `TRIT_NEG;
            default: signed_to_trit = `TRIT_ZERO;
        endcase
    endfunction

    always @(*) begin
        // s = a + b + cin, range [-3, +3]
        // In balanced ternary: result = s mod 3, carry = s / 3
        reg signed [2:0] sa, sb, sc, total;
        sa = trit_to_signed(a);
        sb = trit_to_signed(b);
        sc = trit_to_signed(cin);
        total = sa + sb + sc;

        case(total)
            -3: begin sum = `TRIT_ZERO; cout = `TRIT_NEG; end
            -2: begin sum = `TRIT_POS;  cout = `TRIT_NEG; end
            -1: begin sum = `TRIT_NEG;  cout = `TRIT_ZERO; end
             0: begin sum = `TRIT_ZERO; cout = `TRIT_ZERO; end
             1: begin sum = `TRIT_POS;  cout = `TRIT_ZERO; end
             2: begin sum = `TRIT_NEG;  cout = `TRIT_POS;  end
             3: begin sum = `TRIT_ZERO; cout = `TRIT_POS;  end
            default: begin sum = `TRIT_ZERO; cout = `TRIT_ZERO; end
        endcase
    end
endmodule

/* ======================================================================== */
/*  9-Trit Ripple-Carry Adder                                              */
/* ======================================================================== */
module trit_adder_9(
    input  [`WORD_BITS-1:0] a,
    input  [`WORD_BITS-1:0] b,
    output [`WORD_BITS-1:0] sum,
    output [`TRIT_WIDTH-1:0] carry_out
);
    wire [`TRIT_WIDTH-1:0] carry [`WORD_TRITS:0];
    assign carry[0] = `TRIT_ZERO;

    genvar i;
    generate
        for (i = 0; i < `WORD_TRITS; i = i + 1) begin : ADDER_STAGE
            trit_full_adder fa(
                .a(a[i*`TRIT_WIDTH +: `TRIT_WIDTH]),
                .b(b[i*`TRIT_WIDTH +: `TRIT_WIDTH]),
                .cin(carry[i]),
                .sum(sum[i*`TRIT_WIDTH +: `TRIT_WIDTH]),
                .cout(carry[i+1])
            );
        end
    endgenerate

    assign carry_out = carry[`WORD_TRITS];
endmodule

/* ======================================================================== */
/*  Ternary ALU (supports core ART-9 operations)                           */
/* ======================================================================== */
module trit_alu(
    input  [3:0]              opcode,
    input  [`WORD_BITS-1:0]   rs1_val,
    input  [`WORD_BITS-1:0]   rs2_val,
    output reg [`WORD_BITS-1:0] result,
    output reg                  zero_flag,
    output reg                  neg_flag
);
    wire [`WORD_BITS-1:0] add_result;
    wire [`TRIT_WIDTH-1:0] add_carry;

    /* Negate b: swap POS<->NEG per trit */
    wire [`WORD_BITS-1:0] neg_rs2;
    genvar j;
    generate
        for (j = 0; j < `WORD_TRITS; j = j + 1) begin : NEG_TRIT
            assign neg_rs2[j*2+1] = rs2_val[j*2];
            assign neg_rs2[j*2]   = rs2_val[j*2+1];
        end
    endgenerate

    trit_adder_9 adder(
        .a(rs1_val),
        .b((opcode == `OP_TSUB || opcode == `OP_TCMP) ? neg_rs2 : rs2_val),
        .sum(add_result),
        .carry_out(add_carry)
    );

    /* Kleene min/max per-trit */
    reg [`WORD_BITS-1:0] kleene_result;
    integer k;
    always @(*) begin
        for (k = 0; k < `WORD_TRITS; k = k + 1) begin
            if (opcode == `OP_TAND || opcode == `OP_TMIN) begin
                // min: prefer NEG > ZERO > POS
                if (rs1_val[k*2 +: 2] == `TRIT_NEG || rs2_val[k*2 +: 2] == `TRIT_NEG)
                    kleene_result[k*2 +: 2] = `TRIT_NEG;
                else if (rs1_val[k*2 +: 2] == `TRIT_ZERO || rs2_val[k*2 +: 2] == `TRIT_ZERO)
                    kleene_result[k*2 +: 2] = `TRIT_ZERO;
                else
                    kleene_result[k*2 +: 2] = `TRIT_POS;
            end else begin
                // max: prefer POS > ZERO > NEG
                if (rs1_val[k*2 +: 2] == `TRIT_POS || rs2_val[k*2 +: 2] == `TRIT_POS)
                    kleene_result[k*2 +: 2] = `TRIT_POS;
                else if (rs1_val[k*2 +: 2] == `TRIT_ZERO || rs2_val[k*2 +: 2] == `TRIT_ZERO)
                    kleene_result[k*2 +: 2] = `TRIT_ZERO;
                else
                    kleene_result[k*2 +: 2] = `TRIT_NEG;
            end
        end
    end

    /* Shift left: shift trit positions (insert ZERO at LSB) */
    reg [`WORD_BITS-1:0] shl_result;
    always @(*) begin
        shl_result = {rs1_val[`WORD_BITS-3:0], `TRIT_ZERO};
    end

    /* Shift right: shift trit positions (insert ZERO at MSB) */
    reg [`WORD_BITS-1:0] shr_result;
    always @(*) begin
        shr_result = {`TRIT_ZERO, rs1_val[`WORD_BITS-1:2]};
    end

    /* Negate: swap all trits POS<->NEG */
    reg [`WORD_BITS-1:0] neg_result;
    always @(*) begin
        for (k = 0; k < `WORD_TRITS; k = k + 1) begin
            neg_result[k*2+1] = rs1_val[k*2];
            neg_result[k*2]   = rs1_val[k*2+1];
        end
    end

    /* Result mux */
    always @(*) begin
        result = {`WORD_BITS{1'b0}};
        zero_flag = 0;
        neg_flag = 0;

        case (opcode)
            `OP_TADD:   result = add_result;
            `OP_TSUB:   result = add_result;
            `OP_TCMP:   result = add_result;   // sets flags only
            `OP_TNEG:   result = neg_result;
            `OP_TAND:   result = kleene_result;
            `OP_TOR:    result = kleene_result;
            `OP_TMIN:   result = kleene_result;
            `OP_TMAX:   result = kleene_result;
            `OP_TSHL:   result = shl_result;
            `OP_TSHR:   result = shr_result;
            `OP_TMOVI:  result = rs2_val;      // Immediate loaded via rs2
            `OP_TNOP:   result = {`WORD_BITS{1'b0}};
            default:    result = {`WORD_BITS{1'b0}};
        endcase

        /* Zero flag: all trits are ZERO */
        zero_flag = (result == {`WORD_BITS{1'b0}});

        /* Negative flag: MSB trit is NEG */
        neg_flag = (result[`WORD_BITS-1 -: `TRIT_WIDTH] == `TRIT_NEG);
    end
endmodule

/* ======================================================================== */
/*  5-Stage Pipeline Controller                                            */
/* ======================================================================== */
module art9_pipeline(
    input                clk,
    input                rst_n,
    input  [31:0]        instr_in,       // Instruction word (padded to 32b)
    input                instr_valid,
    output reg           stall,
    output reg           halted,
    output reg [31:0]    cycle_count,
    output reg [31:0]    instr_retired,
    output reg [31:0]    stall_count
);
    /* Register file: 9 GPTRs */
    reg [`WORD_BITS-1:0] regfile [`NUM_REGS-1:0];

    /* Pipeline registers */
    reg [31:0] if_id_instr;
    reg        if_id_valid;

    reg [3:0]             id_ex_opcode;
    reg [`REG_BITS-1:0]   id_ex_rd, id_ex_rs1, id_ex_rs2;
    reg [`WORD_BITS-1:0]  id_ex_val1, id_ex_val2;
    reg                   id_ex_valid;
    reg                   id_ex_writes_rd;

    reg [3:0]             ex_mem_opcode;
    reg [`REG_BITS-1:0]   ex_mem_rd;
    reg [`WORD_BITS-1:0]  ex_mem_result;
    reg                   ex_mem_valid;
    reg                   ex_mem_writes_rd;

    reg [`REG_BITS-1:0]   mem_wb_rd;
    reg [`WORD_BITS-1:0]  mem_wb_result;
    reg                   mem_wb_valid;
    reg                   mem_wb_writes_rd;

    /* Instruction decode fields */
    wire [3:0]           dec_opcode = if_id_instr[31:28];
    wire [`REG_BITS-1:0] dec_rd     = if_id_instr[27:24];
    wire [`REG_BITS-1:0] dec_rs1    = if_id_instr[23:20];
    wire [`REG_BITS-1:0] dec_rs2    = if_id_instr[19:16];

    /* ALU */
    wire [`WORD_BITS-1:0] alu_result;
    wire                  alu_zero, alu_neg;

    trit_alu alu_inst(
        .opcode(id_ex_opcode),
        .rs1_val(id_ex_val1),
        .rs2_val(id_ex_val2),
        .result(alu_result),
        .zero_flag(alu_zero),
        .neg_flag(alu_neg)
    );

    /* RAW hazard detection */
    wire raw_hazard_ex  = id_ex_valid && id_ex_writes_rd &&
                          ((id_ex_rd == dec_rs1) || (id_ex_rd == dec_rs2));
    wire raw_hazard_mem = ex_mem_valid && ex_mem_writes_rd &&
                          ((ex_mem_rd == dec_rs1) || (ex_mem_rd == dec_rs2));
    wire hazard_stall   = if_id_valid && (raw_hazard_ex || raw_hazard_mem);

    /* Does opcode write rd? */
    function writes_register;
        input [3:0] op;
        case(op)
            `OP_TADD, `OP_TSUB, `OP_TMUL, `OP_TNEG,
            `OP_TAND, `OP_TOR, `OP_TMIN, `OP_TMAX,
            `OP_TSHL, `OP_TSHR, `OP_TLOAD, `OP_TMOVI:
                writes_register = 1;
            default:
                writes_register = 0;
        endcase
    endfunction

    integer r;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            /* Reset all pipeline state */
            if_id_valid   <= 0;
            id_ex_valid   <= 0;
            ex_mem_valid  <= 0;
            mem_wb_valid  <= 0;
            halted        <= 0;
            stall         <= 0;
            cycle_count   <= 0;
            instr_retired <= 0;
            stall_count   <= 0;
            for (r = 0; r < `NUM_REGS; r = r + 1)
                regfile[r] <= {`WORD_BITS{1'b0}};
        end else if (!halted) begin
            cycle_count <= cycle_count + 1;

            /* ---- WB stage ---- */
            if (mem_wb_valid && mem_wb_writes_rd) begin
                if (mem_wb_rd < `NUM_REGS)
                    regfile[mem_wb_rd] <= mem_wb_result;
                instr_retired <= instr_retired + 1;
            end else if (mem_wb_valid) begin
                instr_retired <= instr_retired + 1;
            end

            /* ---- MEM stage (pass-through for now) ---- */
            mem_wb_valid     <= ex_mem_valid;
            mem_wb_rd        <= ex_mem_rd;
            mem_wb_result    <= ex_mem_result;
            mem_wb_writes_rd <= ex_mem_writes_rd;

            /* ---- EX stage ---- */
            ex_mem_valid     <= id_ex_valid;
            ex_mem_opcode    <= id_ex_opcode;
            ex_mem_rd        <= id_ex_rd;
            ex_mem_result    <= alu_result;
            ex_mem_writes_rd <= id_ex_writes_rd;

            /* Check for HALT */
            if (id_ex_valid && id_ex_opcode == `OP_THALT)
                halted <= 1;

            /* ---- ID stage ---- */
            if (hazard_stall) begin
                /* Insert bubble */
                id_ex_valid <= 0;
                stall       <= 1;
                stall_count <= stall_count + 1;
                /* Keep IF/ID (don't advance) */
            end else begin
                stall <= 0;
                if (if_id_valid) begin
                    id_ex_opcode    <= dec_opcode;
                    id_ex_rd        <= dec_rd;
                    id_ex_rs1       <= dec_rs1;
                    id_ex_rs2       <= dec_rs2;
                    id_ex_val1      <= (dec_rs1 < `NUM_REGS) ? regfile[dec_rs1] : {`WORD_BITS{1'b0}};
                    id_ex_val2      <= (dec_rs2 < `NUM_REGS) ? regfile[dec_rs2] : {`WORD_BITS{1'b0}};
                    id_ex_valid     <= 1;
                    id_ex_writes_rd <= writes_register(dec_opcode);
                end else begin
                    id_ex_valid <= 0;
                end

                /* ---- IF stage ---- */
                if_id_instr <= instr_in;
                if_id_valid <= instr_valid;
            end
        end
    end
endmodule
