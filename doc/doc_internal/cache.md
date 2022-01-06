# Entity: cache 

- **File**: cache.sv
## Diagram

![Diagram](cache.svg "Diagram")
## Generics

| Generic name | Type | Value | Description            |
| ------------ | ---- | ----- | ---------------------- |
| INPUT        |      | 4     | number of input bytes  |
| OUTPUT       |      | 4     | number of output bytes |
## Ports

| Port name | Direction | Type             | Description                                     |
| --------- | --------- | ---------------- | ----------------------------------------------- |
| clk_i     | input     |                  | system clock                                    |
| rst_in    | input     |                  | system reset, low active                        |
| cfg_stb_i | input     |                  | configure flag, configuration at cfg_i is valid |
| cfg_i     | input     | [INPUT-1:0]      | configure active input bytes                    |
| stb_i     | input     |                  | indicates that input is ready                   |
| d_i       | input     | [(INPUT*8)-1:0]  | input data                                      |
| stb_o     | output    |                  | output is ready                                 |
| q_o       | output    | [(OUTPUT*8)-1:0] | output data                                     |
## Signals

| Name       | Type                           | Description |
| ---------- | ------------------------------ | ----------- |
| state      | states_t                       |             |
| state_next | states_t                       |             |
| cache      | logic [(INPUT+OUTPUT-1)*8-1:0] |             |
| cache_next | logic [(INPUT+OUTPUT-1)*8-1:0] |             |
| cfg        | logic [INPUT-1:0]              |             |
| cnt        | logic [$clog2(INPUT+OUTPUT):0] |             |
| cnt_next   | logic [$clog2(INPUT+OUTPUT):0] |             |
## Types

| Name     | Type                                                                                                                                                                                      | Description |
| -------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------- |
| states_t | enum bit [1:0] {<br><span style="padding-left:20px"> IDLE,<br><span style="padding-left:20px"> TRG,<br><span style="padding-left:20px"> TX,<br><span style="padding-left:20px"> TX_WAIT } |             |
## Processes
- caching: (  )
  - **Type:** always_comb
- assign_output: (  )
  - **Type:** always_comb
- fsm: ( @(posedge clk_i ) )
  - **Type:** always_ff
- set_cfg: ( @(posedge clk_i) )
  - **Type:** always_ff
