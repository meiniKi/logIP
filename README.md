# logIP
Logic analyzer IP core

## Folder Structure
```
.
├── doc             Documentation
├── fv              Formal scripts
├── out             Generated files like bitstreams
├── README.md
├── scripts         Scripts to build, analyze, report, ...
├── sim             Simulation files
├── src             RTL source files and IP cores
├── tb              Testbenches
└── utils           External utils like git submodules

```

# Simulate 
```
cd scripts
./run_sim.sh -d <module_name>
./run_again.sh
```

## Dev
install ```sigrok-firmware-fx2lafw```

https://sigrok.org/wiki/Linux