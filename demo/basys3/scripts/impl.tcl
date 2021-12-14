
set path_origin ../../..

set path_ip_rtl $path_origin/src
set path_output ../out


create_project -in_memory -part xc7a35tcpg236-1 -force $path_output/logIPDemo

read_ip ../ip/gen_main_clk_1/gen_main_clk_1.xci

#
# Generate all the output products
generate_target all [get_files *.xci]
synth_ip [get_files *.xci]

# Read sources
#
read_verilog [ glob ../src/*.sv ]
read_verilog [ glob $path_ip_rtl/.*sv ]
read_xdc ../constr/main.xdc

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

# Write Bitfile
#
write_bitstream $path_output/design.bit

# Append here configuration memory
#
