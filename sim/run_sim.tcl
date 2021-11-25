
set path_origin ../

set path_rtl $path_origin/src/
set path_tb $path_origin/tb/

# Read design sources
add_files -fileset sim_1 [ glob $path_rtl/tuart_r*.sv ]

# Read testbench
add_files -fileset sim_1 {
    ../tb/tb_pkg.sv \
    ../tb/tuart_rx_tb.sv 
}

save_project_as sim -force

set_property top tuart_rx_tb [get_fileset sim_1]
update_compile_order -fileset sim_1
launch_simulation -simset sim_1 -mode behavioral
run -all
exit
