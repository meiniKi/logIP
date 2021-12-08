#! /bin/bash

source ../scripts/source.sh
cd ../sim
vivado -mode batch -source ../scripts/sim_proj.tcl
cd ../scripts