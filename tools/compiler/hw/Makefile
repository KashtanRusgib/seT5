# hw/Makefile - FPGA synthesis Makefile for Ternary Processor
#
# Targets:
#   make sim          - Run Icarus Verilog testbench simulation
#   make sim_full     - Run full processor testbench
#   make synth_ice40  - Synthesize for Lattice iCE40 HX8K (Yosys + nextpnr)
#   make prog_ice40   - Program iCE40 board via iceprog
#   make synth_xilinx - Generate Vivado TCL script for Xilinx Artix-7
#   make clean        - Remove generated files

VERILOG_SRCS = ternary_alu.v ternary_processor_full.v fpga_top.v
TB_BASIC     = ternary_tb.v
TB_FULL      = ternary_processor_full_tb.v

# Tool paths (override via environment)
IVERILOG ?= iverilog
VVP      ?= vvp
YOSYS    ?= yosys
NEXTPNR  ?= nextpnr-ice40
ICEPACK  ?= icepack
ICEPROG  ?= iceprog

# iCE40 device settings
ICE40_DEVICE  ?= hx8k
ICE40_PACKAGE ?= ct256
PCF_FILE      = fpga_constraints.pcf

# Simulation targets
.PHONY: sim sim_full synth_ice40 prog_ice40 synth_xilinx clean

sim: $(TB_BASIC) ternary_alu.v
	$(IVERILOG) -o ternary_alu_tb.vvp $(TB_BASIC) ternary_alu.v
	$(VVP) ternary_alu_tb.vvp

sim_full: $(TB_FULL) $(VERILOG_SRCS)
	$(IVERILOG) -o ternary_proc_tb.vvp $(TB_FULL) ternary_processor_full.v ternary_alu.v
	$(VVP) ternary_proc_tb.vvp

# iCE40 synthesis flow: Yosys → nextpnr → icepack
synth_ice40: $(VERILOG_SRCS) $(PCF_FILE)
	@echo "=== Synthesizing for iCE40 $(ICE40_DEVICE) ==="
	$(YOSYS) -p "read_verilog fpga_top.v ternary_processor_full.v ternary_alu.v; \
	             synth_ice40 -top fpga_top -json ternary_fpga.json"
	$(NEXTPNR) --$(ICE40_DEVICE) --package $(ICE40_PACKAGE) \
	           --json ternary_fpga.json --pcf $(PCF_FILE) \
	           --asc ternary_fpga.asc
	$(ICEPACK) ternary_fpga.asc ternary_fpga.bin
	@echo "=== Bitstream: ternary_fpga.bin ==="

prog_ice40: ternary_fpga.bin
	$(ICEPROG) ternary_fpga.bin

# Xilinx Vivado TCL script generation
synth_xilinx:
	@echo "=== Generating Vivado TCL script ==="
	@echo "# Vivado synthesis script for Ternary Processor"         > vivado_synth.tcl
	@echo "create_project ternary_fpga ./vivado_proj -part xc7a35tcpg236-1" >> vivado_synth.tcl
	@echo "add_files {fpga_top.v ternary_processor_full.v ternary_alu.v}" >> vivado_synth.tcl
	@echo "add_files -fileset constrs_1 fpga_constraints.xdc"       >> vivado_synth.tcl
	@echo "set_property top fpga_top [current_fileset]"              >> vivado_synth.tcl
	@echo "launch_runs synth_1 -jobs 4"                              >> vivado_synth.tcl
	@echo "wait_on_run synth_1"                                      >> vivado_synth.tcl
	@echo "launch_runs impl_1 -to_step write_bitstream -jobs 4"     >> vivado_synth.tcl
	@echo "wait_on_run impl_1"                                       >> vivado_synth.tcl
	@echo "=== Run with: vivado -mode batch -source vivado_synth.tcl ==="

clean:
	rm -f *.vvp *.vcd *.json *.asc *.bin vivado_synth.tcl
	rm -rf vivado_proj
