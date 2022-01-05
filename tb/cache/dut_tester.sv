/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY `WAIT_CYCLES(1, clk_i)

program cache_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");
    #(100)

    TC_DATA_PASSTHROUGH();

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end  

  task TC_DATA_PASSTHROUGH();
    `CLK_DELAY  duv_if.cb.d_i   <= 'h01010101;
                duv_if.cb.stb_i <= 'b1;
    @(posedge duv_if.cb.stb_o);
                duv_if.cb.stb_i <= 'b0;
    `ASSERT_EQ('h01010101, duv_if.cb.q_o);
    `CLK_DELAY  // wait
    `CLK_DELAY  duv_if.cb.d_i   <= 'h02020202;
                duv_if.cb.stb_i <= 'b1;
    @(posedge duv_if.cb.stb_o);
                duv_if.cb.stb_i <= 'b0;
    `ASSERT_EQ('h02020202, duv_if.cb.q_o);
  endtask

endprogram