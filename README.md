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


# Modules

- Module: [core ](./doc/doc_internal/core.md)
- Module: [ctrl ](./doc/doc_internal/ctrl.md)
- Module: [indec ](./doc/doc_internal/indec.md)
- Module: [logIP ](./doc/doc_internal/logIP.md)
- Module: [logIP_pkg ](./doc/doc_internal/logIP_pkg.md)
- Module: [lutram ](./doc/doc_internal/lutram.md)
- Module: [ramif ](./doc/doc_internal/ramif.md)
- Module: [rdback ](./doc/doc_internal/rdback.md)
- Module: [sampler ](./doc/doc_internal/sampler.md)
- Module: [stage ](./doc/doc_internal/stage.md)
- Module: [syncro ](./doc/doc_internal/syncro.md)
- Module: [trigger ](./doc/doc_internal/trigger.md)
- Module: [tuart_rx ](./doc/doc_internal/tuart_rx.md)
- Module: [tuart_tx ](./doc/doc_internal/tuart_tx.md)

