#! /bin/bash

vivadoPath=/tools/Xilinx/Vivado
fileName=settings64.sh

if [ ! -d $vivadoPath ] 
then
    echo "[ERROR] No Vivado installation found. If Vivado is installed in a different directory then default, correct the path in scripts/source.sh."
    exit
fi

versionPaths=($(find $vivadoPath/ -maxdepth 1 -name '20*.*' -type d | sort))
versionPath=${versionPaths[-1]}

if [ -z $versionPath ]
then
    echo "[ERROR] No valid Vivado version found."
    exit
fi

fullPath=$versionPath/$fileName

if [ ! -f $fullPath ]
then
    echo "[ERROR] No valid Vivado installation found."
    exit
fi

source $fullPath
