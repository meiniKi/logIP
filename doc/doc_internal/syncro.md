# Entity: syncro 

- **File**: syncro.sv
## Diagram

![Diagram](syncro.svg "Diagram")
## Generics

| Generic name | Type | Value | Description   |
| ------------ | ---- | ----- | ------------- |
| WIDTH        |      | 32    | signal width  |
| INIT_VAL     |      | 'b0   | initial value |
## Ports

| Port name | Direction | Type        | Description              |
| --------- | --------- | ----------- | ------------------------ |
| clk_i     | input     |             | system clock             |
| rst_in    | input     |             | system reset, low active |
| async_i   | input     | [WIDTH-1:0] | asynchronous input       |
| sync_o    | output    | [WIDTH-1:0] | synchronized output      |
## Signals

| Name  | Type              | Description |
| ----- | ----------------- | ----------- |
| inter | logic [WIDTH-1:0] |             |
## Processes
- unnamed: ( @(posedge clk_i) )
  - **Type:** always_ff
