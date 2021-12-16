/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY `WAIT_CYLCES(1, clk_i)

program mmu_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  initial begin
    $timeformat(-9, 2, " ns", 20);
    $display("----- Started ------");

    duv_if.cb.wrt_i               <= 'b0;
    duv_if.cb.read_i              <= 'b0;

    `WAIT_CYLCES(10, clk_i);
    `CLK_DELAY duv_if.cb.d_i      <= 'h11111112;
    `CLK_DELAY duv_if.cb.wrt_i    <= 'b1;
    `CLK_DELAY duv_if.cb.wrt_i    <= 'b0;
    `CLK_DELAY duv_if.cb.d_i      <= 'h11111113;
    duv_if.cb.wrt_i               <= 'b1;
    `CLK_DELAY duv_if.cb.d_i      <= 'h11111114;
    `CLK_DELAY duv_if.cb.wrt_i    <= 'b0;
    repeat(4) `CLK_DELAY;
    `CLK_DELAY duv_if.cb.read_i   <= 'b1;
    `CLK_DELAY `SCORE_ASSERT(duv_if.cb.d_o == 'h11111114);
    $display("%t", $time);

    `CLK_DELAY `SCORE_ASSERT(duv_if.cb.d_o == 'h11111113);
    $display("%t", $time);
    duv_if.cb.read_i              <= 'b0;
    repeat(4) `CLK_DELAY;
    `CLK_DELAY duv_if.cb.read_i   <= 'b1;
    `CLK_DELAY `SCORE_ASSERT(duv_if.cb.d_o == 'h11111112);
    $display("%t", $time);
    duv_if.cb.read_i              <= 'b0;
    `CLK_DELAY duv_if.cb.d_i      <= 'h22222221;
    duv_if.cb.wrt_i               <= 'b1;
    `CLK_DELAY duv_if.cb.wrt_i    <= 'b0;
    duv_if.cb.read_i              <= 'b1;
    `CLK_DELAY `SCORE_ASSERT(duv_if.cb.d_o == 'h22222221);
    $display("%t", $time);
    duv_if.cb.read_i              <= 'b0;

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
