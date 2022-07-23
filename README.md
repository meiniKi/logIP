# logIP

<p align="center">
  <img src="doc/doc_internal/logIP.svg" width="380"/>
</p>

logIP is a utilization-aware logic analyzer IP core the can be synthesized along the actual design to trace signals in operation. E.g., internal signals of an FPGA design can be observed in regular operation without modifying the design files. logIP is based on the [SUMP](https://sump.org/projects/analyzer/protocol/) protocol and already prepares all required interfaces to implement the fully-featured [OLS extensions](http://dangerousprototypes.com/docs/Logic_Analyzer_core:_Background). While implementations of the [SUMP](https://sump.org/projects/analyzer/protocol/) protocol already exist, the main focus is to adapt the logic analyzer core to specific needs.

This project was originally developed as part of the Design of Real-Time Systems Laboratory at the [Institute of Technical Informatics](https://www.tugraz.at/en/institutes/iti/home/) at Graz University of Technology. 


# Usage
## Instantiation
The following snippet shows an instantiation template of the logIP logic analyzer IP. `CHLS` sets the number of input channels to be synthesized. `MEM_DEPTH` adjusts the size of the sampling memory in bits (`10 = 2^10` samples per channel) and `UART_CLK_PER_BIT` sets the Uart baud -rate relative to the system clock.

```
logIP #(.CHLS(32),
        .MEM_DEPTH(10),
        .UART_CLK_PER_BIT(CLK_PER_BIT)) i_logIP (
  .clk_i    (clk), 
  .rst_in   (rst),
  .chls_i   (chls),
  .rx_i     (uart_rx_i),  
  .tx_o     (uart_tx_o)
);
```
## Block Diagram 
This section aims to illustrate the architecture of the logIP implementation. The block diagrams depict the main interactions between the modules. Please note that many signals are not explicitly drawn due to clarity.
### Top Level View
The top-level instantiates the receiver, transmitter, the RAM, and the logIP core. The core implements the architecture independent logic.

<p align="center">
  <img src="doc/block_top.svg" width="300"/>
</p>

### Core Level View
In the following diagram, the instantiations within the core are depicted.

<p align="center">
  <img src="doc/block_core.svg" width="550"/>
</p>

## Input Channels
Up to 32 input channels are available that can be connected to design signals. The number of channels can be decreased in multiples of eight to save sampling memory. IMPORTANT: De-activation of channel groups are not yet suported. Even when not all channels are synthesized, all channel groups must be activated in the client.

## Sampling Memory
Samples are stored in a sampling memory (RAM) accessed by an interface layer. The handshaking is kept simple to ease modification and extensions. Currently, the RAM can be synthesized of LUT's or (Xilinx) block ram (BRAM). However, changes to use external RAM are also possible. Memory size (in the number of samples) can be set by module parameters.

## Folder Structure
The folder structure is given as follows: `demo` holds demonstration projects that can be synthesized and tested out-of-the-box. `doc` contains all documentation files of logIP. `fv` contains files for formally verifying the design. All generated files, such as the bitstream, reports, etc., are collected in `out`. All scripts to, e.g., run the simulation are located in `scripts`. The design files themselves are placed in `src`. The repository contains an extensive testbench framework put in `tb` along with the design. Finally, `utils` have submodules and the test-pattern generator.

```
.
├── demo            Demo projects
|   └── basys3
├── doc             Documentation
├── fv              Formal scripts
├── out             Generated files like bitstreams
├── README.md
├── scripts         Scripts to build, analyze, report, ...
├── sim             Simulation files
├── src             RTL source files and IP cores
├── tb              Testbenches
└── utils           External utils like git submodules
    └── tpg

```

# Design Documentation
The following table provides a link to the documentation of each module. Note: The HDL itself is documented verbose and meaningful fashion and might help further understand the design.

| Module Name | Usage                     | Documentation                                 |
| ----------- | ------------------------- | --------------------------------------------  |
| logIP       | Top Level, logIP          | [logIP ](./doc/doc_internal/logIP.md)         |
| logIP_pkg   | Package                   | [logIP_pkg ](./doc/doc_internal/logIP_pkg.md) |
| core        | logIP Core                | [core ](./doc/doc_internal/core.md)           |
| ctrl        | Controller, Main FSM      | [ctrl ](./doc/doc_internal/ctrl.md)           |
| indec       | Instruction Decoder       | [indec ](./doc/doc_internal/indec.md)         |
| ramif       | RAM Interface Memory      | [ramif ](./doc/doc_internal/ramif.md)         |
| lutram      | LUT RAM Memory            | [lutram ](./doc/doc_internal/lutram.md)       |
| rdback      | Readback (ID, Metadata)   | [rdback ](./doc/doc_internal/rdback.md)       |
| sampler     | Sampler of Input Channels | [sampler ](./doc/doc_internal/sampler.md)     |
| stage       | Single Trigger Stage      | [stage ](./doc/doc_internal/stage.md)         |
| trigger     | Trigger: 4 Stages         | [trigger ](./doc/doc_internal/trigger.md)     |
| tuart_rx    | (Tiny) UART receiver      | [tuart_rx ](./doc/doc_internal/tuart_rx.md)   |
| tuart_tx    | (Tiny) UART transmitter   | [tuart_tx ](./doc/doc_internal/tuart_tx.md)   |
| syncro      | Synchronizer, legacy      | [syncro ](./doc/doc_internal/syncro.md)       |


# Verification
LogIP has been developed with verification in mind from the early beginning. To achieve desirable confidence of functional correctness, verification is based on two pillars: dynamic verification and formal verification to thoroughly verify critical aspects of the design. 

LogIP shall be considered an easy-to-use logic analyzer block that students may use to debug educational projects. Thus, one requirement is to keep the burden of running verification low. A self-contained simulation framework has been developed to ease simulation runs and avoid further dependencies. Most modules are tested independently using the verification framework and carefully crafted test cases.

As with dynamic verification, the goal was to keep the accessibility of the required tools high and minimize the burden of running verification. However, due to the lack of freely available SVA formal verification tools, the formal flow is split into two parts: one is entirely based on freely available tools and the second one requires a license.

## Simulation

In `/tb` almost all modules come with an individual testbench to verify their behavior. One folder (`frwk`) is reserved for the framework itself. The framework provides helper functions/macros and models a fully-featured client to simulate the end-to-end behavior. In addition, the test framework offers a mailbox-based system to get a summary report of failed assertions.
```
tb/
├── core
├── ctrl
├── frwk       <-- Testbench framework
├── indec
├── logIP
├── sampler
├── stage
├── trigger
├── tuart_rx
└── tuart_tx
```

The structure of each testbench is similar and consists of (at least) four files. 
```
tb/<module>/
├── dut_if.sv
├── dut_tester.sv
├── dut_wrapper.sv
└── <module>_tb.sv
```

`dut_if.sv` provides the interface to the device under test (DUT) and sets the modport and clocking block accordingly. In `dut_wrapper.sv`, the DUT is instantiated and connected to its interface. `dut_tester.sv` applies the test stimuli and monitors the behavior. In `<module>_tb.sv` all parts are instantiated and the main system clock is generated.



A script is provided for convenience to run the testbench for a particular module.
```
cd <repo>/scripts
./run_sim.sh -d <module_name>
./run_again.sh
```

## Formal Verification

SVA model checking is based on the extensions of [yosys](https://github.com/YosysHQ/yosys) by [YosysHQ](https://www.yosyshq.com/). The (mostly) concurrent assertions are placed right before the `endmodule` of each module if properties are present in that module. Placing the assertions in a separate checker that can be bound to the design files has been considered but was omitted as just a few properties exist. `run_formal.sh` in its default configuration runs BMC with a depth of 120 and may be modified and extended.

```
cd <repo>/fv/verific
./run_formal.sh -d <module_name>
```

The (experimental) alternative formal run converts the SystemVerilog files to pure Verilog code using [sv2v](https://github.com/zachjs/sv2v) and afterward runs yosys on the generated output. Thus, verifying properties is currently limited to immediate assertions. However, tools might arise that convert (a subset of) SVA properties to an equivalent Verilog representation.

```
cd <repo>/fv/yosys
./run_formal.sh -d <module_name>
```


# Demos
Demos are placed in `<repo>/demo`.
## Basys3
In this demo, logIP is instantiated and connected to the test-pattern generator. The incoming and outgoing Uart signals are repeated at two I/O pins for debugging.

The following script can start synthesis and implementation. After the script has successfully finished, the bitstream and reports are copied to `<repo>/demo/basys3/out`.
```
cd <repo>/demo/basys3/scripts
./run_impl.sh
```

Another script can be run to program the bitstream into volatile configuration memory.
```
./run_prog.sh
```

# Clients
The following is a non-extensive list of available clients that support the SUMP protocol.
* [Original SUMP Client](https://sump.org/projects/analyzer/)
* [Pulseview / Sigrok](https://sigrok.org/)
* [Open Logic Sniffer](https://github.com/jawi/ols)


# Authors
+ [Meinhard Kissich](https://github.com/meiniKi)
+ [Klaus Weinbauer](https://github.com/klausweinbauer)


# Status
The project was started as part of a university course and was extended to a stable state for educational usage. However, more effort is required to make the IP more versatile, more robust and support the OLS extensions. We are open to interested people who want to contribute to logIP.


# Issues
The [Original SUMP Client](https://sump.org/projects/analyzer/) depends on the RXTX library that can be found [here](http://rxtx.qbang.org/wiki/index.php/Download). Please make sure to use version [rxtx-2.2pre2.zip](http://rxtx.qbang.org/pub/rxtx/rxtx-2.2pre2.zip) and `openjdk-8-jre`. The default java version can be changed by `sudo update-alternatives --config java`.
