/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY `WAIT_CYCLES(1, clk_i)

program core_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");


    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
