
set path_origin ..

set path_rtl    $path_origin/src
set path_tb_dir $path_origin/tb

# Get files for correct testbench
if { $argc != 1 } {
    puts "The sim.tcl script requires a testbench to be executed."
    puts "Please try again."
} else {
    puts [format "Load testbench %s" $argv 0]
}

set dut_name [format "%s" $argv 0]
set top_name [format "%s_tb" $dut_name] 
set path_tb $path_tb_dir/$dut_name

# Read testbench framework
add_files -fileset sim_1 [ glob $path_tb_dir/frwk/*.svh ]
add_files -fileset sim_1 [ glob $path_tb_dir/frwk/*.sv ]

# Read design sources
add_files -fileset sim_1 [ glob $path_rtl/logIP*.sv ]
add_files -fileset sim_1 [ glob $path_rtl/tuart_*.sv ]
add_files -fileset sim_1 [ glob $path_rtl/syncro.sv ]

# Read testbench
add_files -fileset sim_1 [ glob $path_tb/*.sv ]

save_project_as sim -force
set_property top $top_name [get_fileset sim_1]
#update_compile_order -fileset sim_1
launch_simulation -simset sim_1 -mode behavioral
run -all
exit
