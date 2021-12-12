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

rm -f ./artifacts/check.sby
cat <<EOT >> ./artifacts/check.sby
[tasks]
task_bmc

[options]
task_bmc:
mode bmc
depth 100

[engines]
smtbmc

[script]
read -formal $parameterDut.v
prep -top top_$parameterDut

[files]
./artifacts/$parameterDut.v
EOT

rm -f ./artifacts/$parameterDut.v
sv2v --define=FORMAL -E assert --write=./artifacts/$parameterDut.v ./wrapper/wrap_$parameterDut.sv ../src/$parameterDut.sv ../src/logIP_pkg.sv ../src/logIP_ifs.sv
sby -f ./artifacts/check.sby 