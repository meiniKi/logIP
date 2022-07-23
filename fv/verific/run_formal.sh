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

mkdir artifacts
rm -f ./artifacts/check.sby
cat <<EOT >> ./artifacts/check.sby
# Simple SymbiYosys example job utilizing Verific

[options]
mode bmc
depth 120

[engines]
smtbmc yices

[script]
verific -formal $parameterDut.sv
verific -import $parameterDut
prep -top $parameterDut

[files]
../../src/$parameterDut.sv
EOT

sby -f ./artifacts/check.sby 