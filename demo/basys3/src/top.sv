/*
 * file: top.sv
 * usage: Demo top level
 *
 */

module top (
  input  logic clk,
  //
  // external Test-Channels here
  //

  // Uart Communication
  input  logic uart_rx_i,
  output logic uart_tx_o
);

  localparam CLK_PER_BIT = 100_000_000 / 115_200;

  logic         sys_clk;
  logic         rst;
  logic         lckd;
  logic [31:0]  chls;

  sys_clk_gen i_sys_clk_gen
  (
    .sys_clk  (sys_clk),
    .reset    (rst),
    .locked   (lckd),
    .clk_in1  (clk)
  );

  logIP #(.WIDTH(32),
          .UART_CLK_PER_BIT(CLK_PER_BIT)) i_logIP (
    .clk_i    (sys_clk), 
    .rst_in   (rst),
    .chls_i   (chls),
    .rx_i     (uart_rx_i),  
    .tx_o     (uart_tx_o)
  );

  // TODO: instatiate test pattern generator

endmodule

