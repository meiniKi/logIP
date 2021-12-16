/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY #(CLK_PERIOD_HALF*2)
`define SMPL_DELAY #(CLK_PERIOD_HALF*10)

program ctrl_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  logic [31:0] smpls_i        = 'b0;
  logic [31:0] smpls_start;
  logic [31:0] expected_d_o = 'b0;
  logic [2:0]  read_cnt       = 'b1;
  logic [31:0] smpls_trg;

  initial begin
    // Upcounting input signal
    forever begin
      `SMPL_DELAY duv_if.cb.smpls_i <= smpls_i;
      duv_if.cb.stb_i               <= 'b1;
      `CLK_DELAY duv_if.cb.stb_i    <= 'b0;
      smpls_i <= smpls_i + 1;
    end
  end

  initial begin
    $display("----- Started ------");

    #(CLK_PERIOD_HALF*20)

    // Configure controller
    `CLK_DELAY  
    duv_if.cb.cmd_i       <= 'h00040002;
    duv_if.cb.set_cnt_i   <= 'b1;
    `CLK_DELAY
    duv_if.cb.set_cnt_i   <= 'b0;

    

    // TODO
    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
