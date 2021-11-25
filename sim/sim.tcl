
set path_origin ../

set path_rtl $path_origin/src/
set path_tb $path_origin/tb

# Read design sources
add_files -fileset sim_1 [ glob $path_rtl/lwc_api/*.sv ]
add_files -fileset sim_1 [ glob $path_rtl/ascon/*.vhd ]

# Read testbench
add_files -fileset sim_1 {
    ./tb/dut_if.sv \
    ./tb/dut_wrapper.sv \
    ./tb/cipher_tb_pkg.sv \
    ./tb/cipher_tb.sv \
    ./tb/tb_top.sv
}

save_project_as sim -force

set_property top tb_top [get_fileset sim_1]
update_compile_order -fileset sim_1
launch_simulation -simset sim_1 -mode behavioral
run -all
exit
