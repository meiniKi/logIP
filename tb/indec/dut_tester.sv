/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
program indec_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    // Test asserts
    `SCORE_ASSERT(1)
    `SCORE_ASSERT(0)
    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
