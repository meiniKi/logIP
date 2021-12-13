#! /bin/bash

helpFunction()
{
  echo ""
  echo "Usage: $0 -d name"
  echo -e "\t-d Name of the module to simulate"
  exit 1 # Exit script after printing help
}

while getopts "d:" opt
do
  case "$opt" in
    d ) parameterDut="$OPTARG" ;;
    ? ) helpFunction ;; # Print helpFunction in case parameter is non-existent
  esac
done

# Print helpFunction in case parameters are empty
if [ -z "$parameterDut" ]
then
  echo "Some or all of the parameters are empty";
  helpFunction
fi

simDirectory=../sim
if [ ! -d $simDirectory ]
then
  mkdir $simDirectory
  exit
fi

source ../scripts/source.sh
cd $simDirectory
vivado -mode batch -source ../scripts/sim_create.tcl -tclargs $parameterDut
cd ../scripts