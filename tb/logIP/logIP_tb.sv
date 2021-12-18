/*
 * file: logIP_tb.sv
 * usage: Testbench for logIP.sv
 * 
 */

`include "declarations.svh"
`include "uart8.svh"
`default_nettype wire
`timescale 1ns/1ps

module logIP_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;

  Scoreboard      i_scoreboard;
  Client          i_client;
  Uart8           i_uart8;
  score_mbox_t    mbx;       

  initial begin
    // Dump
    $dumpfile("logIP_tb.vcd");
    $dumpvars(5, duv_wrapper);

    // Reset            
    #(10*CLK_PERIOD_HALF) rst_in = 0;
    #(2*CLK_PERIOD_HALF)  rst_in = 1;
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  dut_if duv_if (clk_i, rst_in);
  dut_wrapper duv_wrapper (duv_if.duv);
  logIP_tester duv_tester(duv_if.tb, clk_i, mbx, i_client);

  initial begin
    mbx = new();
    i_scoreboard  = new (mbx);
    i_uart8       = new (30); 
    i_client      = new (i_uart8);

    fork
      i_scoreboard.run();
      i_uart8.run_transmitter(duv_if.rx_i);
      i_uart8.run_receiver(duv_if.tx_o);
      // append
    join
  end

endmodule



