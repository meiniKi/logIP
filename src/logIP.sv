/*
 * file: logIP.sv
 * usage: Top level module for logIP.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module logIP #( parameter WIDTH = 32,
                parameter UART_CLK_PER_BIT = 10,
                parameter MEM_DEPTH = 5
) (
  input  logic              clk_i,    //! system clock
  input  logic              rst_in,   //! system reset
  input  logic [WIDTH-1:0]  chls_i,   //! input channels
  input  logic              rx_i,     //! uart receive
  output logic              tx_o      //! uart transmit
);

  localparam UART_WORD_BITS = 8;
  localparam OPCODE_WORDS   = 1;
  localparam UART_RX_WORDS  = 5;
  localparam UART_TX_WORDS  = 4;
  localparam CORE_WIDTH     = 32;

  localparam RX_WIDTH   = UART_WORD_BITS * UART_RX_WORDS;

  logic [CORE_WIDTH-1:0] chls_padded;

  logic [RX_WIDTH-1:0]    rx_cmd;
  logic                   exec_cmd;

  logic                   mem_we;
  logic [MEM_DEPTH-1:0]   mem_addr;
  logic [MEM_DEPTH-1:0]   mem_din;
  logic [CORE_WIDTH-1:0]  mem_din_padded;
  logic [MEM_DEPTH-1:0]   mem_dout;
  logic [CORE_WIDTH-1:0]  mem_dout_padded;



  assign tx_o = rx_i;
  // TODO

  // The core always takes a fixed-length vector of the input channels 
  // (currently 32 channels according to the sump protocol). This is a
  // design decision due to possible side-effects when the number of 
  // channels is smaller. However, the width of the ram matches the 
  // "real" synthesized number as channels, as this has the most impact
  // on the area. Note: When introducing "fake RLE" in the core, this 
  // might need to be disabled.
  //
  assign chls_padded      = CORE_WIDTH'(chls_i);
  assign mem_din          = mem_din_padded[MEM_DEPTH-1:0];
  assign mem_dout_padded  = CORE_WIDTH'(mem_dout);

  tuart_tx #( .WORD_BITS      (UART_WORD_BITS),
              .CMD_WORDS      (UART_TX_WORDS),
              .CLK_PER_SAMPLE (UART_CLK_PER_BIT)) i_tuart_tx ( 
  .clk_i        (clk_i),
  .rst_in       (rst_in),
  .stb_i        (),
  .rdy_o        (),
  .tx_o         (tx_o),
  .xstb_i       (),
  .xoff_i       (),
  .xon_i        (),
  .data_i       ()
  );

  tuart_rx #( .WORD_BITS      (UART_WORD_BITS),
              .CMD_WORDS      (UART_RX_WORDS),
              .CLK_PER_SAMPLE (UART_CLK_PER_BIT)) i_tuart_rx (
    .clk_i      (clk_i),
    .rst_in     (rst_in),
    .rx_i       (rx_i)
    .data_o,    (rx_cmd),
    .stb_o      (exec_cmd)
  );

  core #( .DEPTH(MEM_DEPTH)) i_core (
    .clk_i      (clk_i), 
    .rst_in,    (rst_in),
    .input_i,   (chls_i),
    .cmd_i,     (rx_cmd),
    .exec_i,    (exec_cmd),
    .we_o,      (mem_we),
    .addr_o,    (mem_addr),
    .mem_i,     (mem_din_padded),
    .mem_o,     (mem_dout_padded),
    .tx_rdy_i,  (),
    .tx_stb_o,  (),
    .tx_o,      (),  
  );

  ramif #(  .WIDTH(WIDTH)
            .DEPTH(MEM_DEPTH)) i_ramif (
    .clk_i      (clk_i),    
    .rst_in     (rst_in),   
    .en_i       ('b1),     
    .we_i       (mem_we),     
    .addr_i     (mem_addr),   
    .d_i        (),      
    .q_o        ()     
  );


endmodule