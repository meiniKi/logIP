/*
 * file: logIP.sv
 * usage: Top level module for logIP.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module logIP #( parameter CHLS = 32,
                parameter UART_CLK_PER_BIT = 10,
                parameter MEM_DEPTH = 5
) (
  input  logic              clk_i,    //! system clock
  input  logic              rst_in,   //! system reset
  input  logic [CHLS-1:0]   chls_i,   //! input channels
  input  logic              rx_i,     //! uart receive
  output logic              tx_o      //! uart transmit
);

  localparam UART_WORD_BITS = 8;
  localparam OPC_WORDS      = 1;
  localparam CMD_WORDS      = 4;
  localparam CORE_WIDTH     = 32;

  localparam CMD_WIDTH      = UART_WORD_BITS * CMD_WORDS;
  localparam OPC_WIDTH      = UART_WORD_BITS * OPC_WORDS;

  logic [CORE_WIDTH-1:0] chls_padded;

  logic [CMD_WIDTH-1:0]   rx_cmd;
  logic [OPC_WIDTH-1:0]   rx_opc;
  logic                   exec_cmd;

  logic [CMD_WIDTH-1:0]   tx_data;
  logic                   tx_stb;
  logic                   tx_rdy;
  logic                   tx_xon;
  logic                   tx_xoff;

  logic                   mem_we;
  logic [MEM_DEPTH-1:0]   mem_addr;
  logic [CHLS-1:0]        mem_din;
  logic [CORE_WIDTH-1:0]  mem_din_padded;
  logic [CHLS-1:0]        mem_dout;
  logic [CORE_WIDTH-1:0]  mem_dout_padded;

  // The core always takes a fixed-length vector of the input channels 
  // (currently 32 channels according to the sump protocol). This is a
  // design decision due to possible side-effects when the number of 
  // channels is smaller. However, the width of the ram matches the 
  // "real" synthesized number as channels, as this has the most impact
  // on the area. Note: When introducing "fake RLE" in the core, this 
  // might need to be disabled.
  //
  assign chls_padded      = CORE_WIDTH'(chls_i);
  assign mem_din          = mem_din_padded[CHLS-1:0];
  assign mem_dout_padded  = CORE_WIDTH'(mem_dout);

  tuart_tx #( .WORD_BITS      (UART_WORD_BITS),
              .CMD_WORDS      (CMD_WORDS),
              .CLK_PER_SAMPLE (UART_CLK_PER_BIT)) i_tuart_tx ( 
    .clk_i      (clk_i),
    .rst_in     (rst_in),
    .stb_i      (tx_stb),
    .rdy_o      (tx_rdy),
    .tx_o       (tx_o),
    .xstb_i     (exec_cmd),
    .xoff_i     (tx_xoff),
    .xon_i      (tx_xon),
    .data_i     (tx_data),
    .sel_i      ('d4)
  );

  tuart_rx #( .WORD_BITS      (UART_WORD_BITS),
              .CMD_WORDS      (CMD_WORDS),
              .CLK_PER_SAMPLE (UART_CLK_PER_BIT)) i_tuart_rx (
    .clk_i      (clk_i),
    .rst_in     (rst_in),
    .rx_i       (rx_i),
    .opc_o      (rx_opc),
    .cmd_o      (rx_cmd),
    .stb_o      (exec_cmd)
  );

  core #( .DEPTH(MEM_DEPTH)) i_core (
    .clk_i      (clk_i), 
    .rst_in     (rst_in),
    .input_i    (chls_padded),
    .opc_i      (rx_opc),
    .cmd_i      (rx_cmd),
    .exec_i     (exec_cmd),
    .we_o       (mem_we),
    .addr_o     (mem_addr),
    .mem_i      (mem_dout_padded),
    .mem_o      (mem_din_padded),
    .tx_rdy_i   (tx_rdy),
    .tx_stb_o   (tx_stb),
    .tx_o       (tx_data),
    .tx_xon_o   (tx_xon),
    .tx_xoff_o  (tx_xoff)
  );

  ramif #(  .WIDTH(CHLS),
            .DEPTH(MEM_DEPTH)) i_ramif (
    .clk_i      (clk_i),    
    .rst_in     (rst_in),   
    .en_i       ('b1),     
    .we_i       (mem_we),     
    .addr_i     (mem_addr),   
    .d_i        (mem_din),      
    .q_o        (mem_dout)     
  );


endmodule