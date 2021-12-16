/*
 * file: trigger_tb.sv
 * usage: Testbench for trigger.sv
 * 
 */

`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

module trigger_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;

  Scoreboard      i_scoreboard;
  score_mbox_t    mbx;       

  initial begin
    // Dump
    $dumpfile("trigger_tb.vcd");
    $dumpvars(5, duv_wrapper);

    // Reset            
    `WAIT_CYCLES(2, clk_i) rst_in = 0;
    `WAIT_CYCLES(2, clk_i) rst_in = 1;
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  dut_if duv_if (clk_i, rst_in);
  dut_wrapper duv_wrapper (duv_if.duv);
  trigger_tester duv_tester(duv_if.tb, clk_i, mbx);

  initial begin
    mbx = new();
    i_scoreboard = new (mbx);

    fork
      i_scoreboard.run();
      // append
    join
  end

endmodule



