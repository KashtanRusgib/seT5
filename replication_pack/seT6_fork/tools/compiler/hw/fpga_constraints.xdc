## fpga_constraints.xdc - Xilinx Artix-7 (Basys3 / Arty) Pin Constraints
##
## Pin assignments for Digilent Basys3 or similar Artix-7 boards.
## Adjust for your specific board.

## Clock (100 MHz on Basys3)
set_property -dict {PACKAGE_PIN W5 IOSTANDARD LVCMOS33} [get_ports clk_in]
create_clock -period 10.000 -name sys_clk_pin -waveform {0.000 5.000} -add [get_ports clk_in]

## Reset (active-low push button)
set_property -dict {PACKAGE_PIN U18 IOSTANDARD LVCMOS33} [get_ports rst_n]

## Program load interface
set_property -dict {PACKAGE_PIN V17 IOSTANDARD LVCMOS33} [get_ports prog_clk]
set_property -dict {PACKAGE_PIN V16 IOSTANDARD LVCMOS33} [get_ports prog_data]
set_property -dict {PACKAGE_PIN W16 IOSTANDARD LVCMOS33} [get_ports prog_load]

## LEDs
set_property -dict {PACKAGE_PIN U16 IOSTANDARD LVCMOS33} [get_ports {led[0]}]
set_property -dict {PACKAGE_PIN E19 IOSTANDARD LVCMOS33} [get_ports {led[1]}]
set_property -dict {PACKAGE_PIN U19 IOSTANDARD LVCMOS33} [get_ports {led[2]}]
set_property -dict {PACKAGE_PIN V19 IOSTANDARD LVCMOS33} [get_ports {led[3]}]
set_property -dict {PACKAGE_PIN W18 IOSTANDARD LVCMOS33} [get_ports {led[4]}]

## UART TX (directly to USB-UART bridge)
set_property -dict {PACKAGE_PIN A18 IOSTANDARD LVCMOS33} [get_ports uart_tx]
