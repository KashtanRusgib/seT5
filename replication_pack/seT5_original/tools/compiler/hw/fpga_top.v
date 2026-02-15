/*
 * fpga_top.v - FPGA Top-Level Wrapper for Ternary Processor (Phase 4)
 *
 * Synthesis-ready top module for Lattice iCE40 or Xilinx Artix-7.
 * Provides:
 *   - Clock divider for slower execution observation
 *   - Program loading via SPI-like serial interface
 *   - LED status outputs (halted, stack depth indicators)
 *   - UART TX for result output (optional)
 *
 * Pin assignments are in fpga_constraints.pcf (iCE40) and
 * fpga_constraints.xdc (Xilinx).
 */

`timescale 1ns/1ps

module fpga_top(
    input  wire       clk_in,     /* Board oscillator (e.g., 12 MHz iCE40) */
    input  wire       rst_n,      /* Active-low reset button */

    /* Program load interface (directly from host) */
    input  wire       prog_clk,   /* Serial clock for program loading */
    input  wire       prog_data,  /* Serial data */
    input  wire       prog_load,  /* Assert to start loading program */

    /* Status LEDs */
    output wire [4:0] led,        /* LED[0]=running, LED[1]=halted, LED[2:4]=stack depth */

    /* Result output (active after halt) */
    output wire       uart_tx     /* Optional UART transmit for result */
);

    /* ---- Clock divider ---- */
    reg [23:0] clk_div;
    wire proc_clk;

    always @(posedge clk_in or negedge rst_n) begin
        if (!rst_n)
            clk_div <= 24'd0;
        else
            clk_div <= clk_div + 1;
    end

    /* Processor runs at clk_in / 2^4 for visibility, or full speed for production */
    assign proc_clk = clk_div[3]; /* ~750 KHz at 12 MHz input */

    /* ---- Internal reset ---- */
    wire internal_rst = ~rst_n;

    /* ---- Program loader (serial to parallel shift register) ---- */
    reg [7:0]  load_shift;
    reg [2:0]  load_bit;
    reg [7:0]  load_addr;
    reg        load_we;
    reg [7:0]  load_data;
    reg        loading;

    always @(posedge prog_clk or posedge internal_rst) begin
        if (internal_rst) begin
            load_shift <= 8'd0;
            load_bit <= 3'd0;
            load_addr <= 8'd0;
            load_we <= 1'b0;
            loading <= 1'b0;
        end else if (prog_load) begin
            loading <= 1'b1;
            load_shift <= {load_shift[6:0], prog_data};
            load_bit <= load_bit + 1;
            load_we <= 1'b0;

            if (load_bit == 3'd7) begin
                load_data <= {load_shift[6:0], prog_data};
                load_we <= 1'b1;
                load_addr <= load_addr + 1;
            end
        end else begin
            loading <= 1'b0;
            load_we <= 1'b0;
        end
    end

    /* ---- Processor instance ---- */
    wire [17:0] tos;
    wire        proc_halted;
    wire [7:0]  proc_pc;

    ternary_processor_full proc(
        .clk(proc_clk),
        .rst(internal_rst | loading),
        .prog_we(load_we),
        .prog_addr(load_addr - 1),
        .prog_data(load_data),
        .top_of_stack(tos),
        .halted(proc_halted),
        .pc_out(proc_pc)
    );

    /* ---- LED assignments ---- */
    assign led[0] = ~proc_halted & ~loading;  /* Running */
    assign led[1] = proc_halted;              /* Halted */
    assign led[2] = tos[1:0] != 2'b00;        /* TOS trit[0] nonzero */
    assign led[3] = tos[3:2] != 2'b00;        /* TOS trit[1] nonzero */
    assign led[4] = tos[5:4] != 2'b00;        /* TOS trit[2] nonzero */

    /* ---- UART TX stub (minimal, 9600 baud at 12 MHz) ---- */
    reg [9:0]  uart_shift;
    reg [3:0]  uart_bit;
    reg [12:0] uart_div;      /* Clock divider: 12M / 9600 ≈ 1250 */
    reg        uart_active;

    assign uart_tx = uart_active ? uart_shift[0] : 1'b1; /* Idle high */

    always @(posedge clk_in or posedge internal_rst) begin
        if (internal_rst) begin
            uart_active <= 1'b0;
            uart_bit <= 4'd0;
            uart_div <= 13'd0;
            uart_shift <= 10'h3FF;
        end else if (proc_halted && !uart_active) begin
            /* Start transmitting result byte (low 8 bits of TOS) */
            uart_active <= 1'b1;
            uart_shift <= {1'b1, tos[7:0], 1'b0}; /* Stop, data, start */
            uart_bit <= 4'd0;
            uart_div <= 13'd0;
        end else if (uart_active) begin
            uart_div <= uart_div + 1;
            if (uart_div == 13'd1249) begin
                uart_div <= 13'd0;
                uart_shift <= {1'b1, uart_shift[9:1]};
                uart_bit <= uart_bit + 1;
                if (uart_bit == 4'd9)
                    uart_active <= 1'b0;
            end
        end
    end

endmodule
