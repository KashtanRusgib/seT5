# T-015: FPGA Timing Report Stubs
#
# Xilinx Artix-7 (xc7a35t) and Lattice iCE40UP5K timing constraints
# for the ternary CPU core.
#
# Usage:
#   vivado -mode batch -source hw/fpga_timing_artix7.xdc  (Xilinx)
#   nextpnr-ice40 --pcf hw/fpga_timing_ice40.pcf          (Lattice)
#

# ═══════════════════════════════════════════════════════════════
# Xilinx Artix-7 Timing Constraints (Vivado XDC format)
# Target: xc7a35tcpg236-1 (Basys 3 / Arty)
# ═══════════════════════════════════════════════════════════════

# 100 MHz system clock
create_clock -period 10.000 -name sys_clk [get_ports clk]

# Clock jitter
set_input_jitter sys_clk 0.100

# Input delay constraints (PAM-3 receiver) — 2ns setup, 1ns hold
set_input_delay -clock sys_clk -max 2.000 [get_ports {pam3_rx[*]}]
set_input_delay -clock sys_clk -min 1.000 [get_ports {pam3_rx[*]}]

# Output delay constraints (memory interface)
set_output_delay -clock sys_clk -max 3.000 [get_ports {mem_addr[*]}]
set_output_delay -clock sys_clk -max 3.000 [get_ports {mem_wdata[*]}]
set_output_delay -clock sys_clk -max 2.000 [get_ports {mem_we mem_re}]

# False paths for reset
set_false_path -from [get_ports rst_n]

# Multi-cycle paths for TCAM (2 cycles for CAM comparison)
set_multicycle_path 2 -setup -from [get_cells -hier -filter {NAME =~ *tcam_table*}]
set_multicycle_path 1 -hold  -from [get_cells -hier -filter {NAME =~ *tcam_table*}]

# Max frequency target: 100 MHz (10ns period)
# Expected: WNS ≥ 0.5ns with balanced ternary ALU critical path

# ═══════════════════════════════════════════════════════════════
# Timing Budget Summary (estimated)
# ═══════════════════════════════════════════════════════════════
#
# Module                   | Est. Logic Levels | Est. Delay (ns)
# ─────────────────────────|───────────────────|─────────────────
# Ternary ALU (AND/OR/NOT) |        3          |     2.1
# Balanced Ternary Adder   |        6          |     4.2
# Wallace-tree Multiplier  |        8          |     5.8
# TCAM Crossbar (16 rows)  |        5          |     3.5
# PAM-3 Decoder            |        2          |     1.4
# Sense Amplifier          |        4          |     2.8
# Register File (9 regs)   |        2          |     1.6
# ─────────────────────────|───────────────────|─────────────────
# Critical Path: Multiplier|        8          |     5.8 ns
# Slack at 100 MHz:        |                   |     4.2 ns ✓
