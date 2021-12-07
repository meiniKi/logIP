
set path_origin ../

set path_rtl $path_origin/src/
set path_tb $path_origin/tb/

# Read design sources
add_files -fileset sim_1 [ glob $path_rtl/logIP*.sv ]
add_files -fileset sim_1 [ glob $path_rtl/tuart_*.sv ]
add_files -fileset sim_1 [ glob $path_rtl/syncro.sv ]

# Read testbench(es)
add_files -fileset sim_1 [ glob $path_tb/*.sv ]
#add_files -fileset sim_1 [ glob $path_tb/tuart_rx/*.sv ]
add_files -fileset sim_1 [ glob $path_tb/tuart_tx/*.sv ]


save_project_as sim -force

set_property top tuart_tx_tb [get_fileset sim_1]
update_compile_order -fileset sim_1
launch_simulation -simset sim_1 -mode behavioral
run -all
exit
