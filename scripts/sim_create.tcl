
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

# Read design sources
add_files -fileset sim_1 [ glob $path_rtl/logIP*.sv ]
add_files -fileset sim_1 [ glob $path_rtl/tuart_*.sv ]
add_files -fileset sim_1        $path_rtl/rdback.sv
add_files -fileset sim_1        $path_rtl/indec.sv
add_files -fileset sim_1        $path_rtl/syncro.sv
add_files -fileset sim_1        $path_rtl/sampler.sv
add_files -fileset sim_1        $path_rtl/stage.sv
add_files -fileset sim_1        $path_rtl/ctrl.sv
add_files -fileset sim_1        $path_rtl/ramif.sv
add_files -fileset sim_1        $path_rtl/lutram.sv
add_files -fileset sim_1        $path_rtl/trigger.sv
add_files -fileset sim_1        $path_rtl/core.sv

# Read testbench framework
add_files -fileset sim_1 [ glob $path_tb_dir/frwk/*.svh ]
add_files -fileset sim_1 [ glob $path_tb_dir/frwk/*.sv ]
add_files -fileset sim_1 $path_tb_dir/frwk/client/uart8.svh
add_files -fileset sim_1 $path_tb_dir/frwk/client/uart8.sv
add_files -fileset sim_1 $path_tb_dir/frwk/client/client.sv

# Read testbench
add_files -fileset sim_1 [ glob $path_tb/*.sv ]

save_project_as sim -force
set_property top $top_name [get_fileset sim_1]

#
# Todo: auto update compile order seems to not work correctly.
#
#update_compile_order -fileset sim_1
launch_simulation -simset sim_1 -mode behavioral
run -all
exit
