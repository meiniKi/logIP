
set path_origin ..

set path_sim    $path_origin/sim/sim.xpr

open_project $path_sim
launch_simulation -simset sim_1 -mode behavioral
run -all
exit
