/*
 * file: top.sv
 * usage: Demo top level
 *
 */

module top (
  input  logic clk,
  //
  // Test-Channels here
  //

  // Uart Communication
  input  logic uart_rx_i,
  output logic uart_tx_o
);

logic sys_clk;
logic rst;
logic lckd;

gen_main_clk i_gen_main_clk
(
 .clk_out1  (sys_clk),
 .reset     (rst),
 .locked    (lckd),
 .clk_in1   (clk)
);

// TODO: instantiate logIP

// TODO: instatiate test pattern generator

endmodule

