
set path_origin ../../..

set path_ip_rtl $path_origin/src
set path_utils  $path_origin/utils
set path_output ../out


create_project -in_memory -part xc7a35tcpg236-1 -force $path_output/logIPDemo ../out/

read_ip ../ip/sys_clk_gen/sys_clk_gen.xci

#
# Generate all the output products
generate_target all [get_files *.xci]
synth_ip [get_files *.xci]

# Read sources
#
read_verilog        $path_utils/tpg/tpg.sv
read_verilog        ../src/top.sv
read_verilog [ glob $path_ip_rtl/*.sv ]
read_xdc ../constr/main.xdc

update_compile_order -verbose

# Synthesis and Implementation
#
synth_design -top top
opt_design
place_design
route_design

# Reports
# 
report_timing_summary -file $path_output/post_route_timing_summary.rpt
report_utilization -file $path_output/post_route_util.rpt

# Config
#
set_property config_mode SPIx4 [current_design]

# Write Bitfile
#
write_bitstream -force $path_output/design.bit
write_cfgmem -format mcs -size 64 -interface SPIx4 -loadbit "up 0x0 $path_output/design.bit" -checksum -force -file $path_output/design.mcs

# Append here configuration memory
#
