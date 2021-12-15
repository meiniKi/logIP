/*
 * file: tuart_tx_tb.sv
 * usage: Testbench for tuart_tx_tb.sv
 * 
 */

`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

module tuart_tx_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;

  Scoreboard      i_scoreboard;
  score_mbox_t    mbx;    

  initial begin
    // Dump
    $dumpfile("tuart_tx_tb.vcd");
    $dumpvars(5, duv_wrapper);

    // Reset            
    `WAIT_CYLCES(2, clk_i)  rst_in = 0;
    `WAIT_CYLCES(2, clk_i)  rst_in = 1;
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  dut_if duv_if (clk_i, rst_in);
  dut_wrapper duv_wrapper (duv_if);
  uart_tx_tester duv_tester (duv_if, clk_i, mbx);

  initial begin
    mbx = new();
    i_scoreboard = new (mbx);

    fork
      i_scoreboard.run();
      // append
    join
  end

endmodule



