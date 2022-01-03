# Entity: logIP 

- **File**: logIP.sv
## Diagram

![Diagram](logIP.svg "Diagram")
## Generics

| Generic name     | Type | Value | Description |
| ---------------- | ---- | ----- | ----------- |
| CHLS             |      | 32    |             |
| UART_CLK_PER_BIT |      | 10    |             |
| MEM_DEPTH        |      | 5     |             |
## Ports

| Port name | Direction | Type       | Description    |
| --------- | --------- | ---------- | -------------- |
| clk_i     | input     |            | system clock   |
| rst_in    | input     |            | system reset   |
| chls_i    | input     | [CHLS-1:0] | input channels |
| rx_i      | input     |            | uart receive   |
| tx_o      | output    |            | uart transmit  |
## Signals

| Name            | Type                   | Description |
| --------------- | ---------------------- | ----------- |
| chls_padded     | logic [CORE_WIDTH-1:0] |             |
| rx_cmd          | logic [CMD_WIDTH-1:0]  |             |
| rx_opc          | logic [OPC_WIDTH-1:0]  |             |
| exec_cmd        | logic                  |             |
| tx_data         | logic [CMD_WIDTH-1:0]  |             |
| tx_stb          | logic                  |             |
| tx_rdy          | logic                  |             |
| tx_xon          | logic                  |             |
| tx_xoff         | logic                  |             |
| mem_we          | logic                  |             |
| mem_addr        | logic [MEM_DEPTH-1:0]  |             |
| mem_din         | logic [CHLS-1:0]       |             |
| mem_din_padded  | logic [CORE_WIDTH-1:0] |             |
| mem_dout        | logic [CHLS-1:0]       |             |
| mem_dout_padded | logic [CORE_WIDTH-1:0] |             |
## Constants

| Name           | Type | Value                      | Description |
| -------------- | ---- | -------------------------- | ----------- |
| UART_WORD_BITS |      | 8                          |             |
| OPC_WORDS      |      | 1                          |             |
| CMD_WORDS      |      | 4                          |             |
| CORE_WIDTH     |      | 32                         |             |
| CMD_WIDTH      |      | UART_WORD_BITS * CMD_WORDS |             |
| OPC_WIDTH      |      | UART_WORD_BITS * OPC_WORDS |             |
## Instantiations

- i_tuart_tx: tuart_tx
- i_tuart_rx: tuart_rx
- i_core: core
- i_ramif: ramif
