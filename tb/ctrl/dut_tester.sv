/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY `WAIT_CYLCES(1, clk_i)
`define SMPL_DELAY `WAIT_CYLCES(4, clk_i)

program ctrl_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  logic [31:0] smpls_i        = 'b0;
  logic [31:0] smpl_trg;

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

    duv_if.cb.tx_rdy_i          <= 'b1;

    #(CLK_PERIOD_HALF*20)

    // Configure controller
    `CLK_DELAY  
    duv_if.cb.cmd_i             <= 'h00040002;
    duv_if.cb.set_cnt_i         <= 'b1;
    `CLK_DELAY
    duv_if.cb.set_cnt_i         <= 'b0;

    `WAIT_CYLCES(8, clk_i);
    duv_if.cb.run_i             <= 'b1;
    smpl_trg                    <= smpls_i;
    `CLK_DELAY duv_if.cb.run_i  <= 'b0;

    @(posedge duv_if.cb.tx_stb_o);
    duv_if.cb.tx_rdy_i          <= 'b0;
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg + 2);
    `WAIT_CYLCES(4, clk_i);
    duv_if.cb.tx_rdy_i          <= 'b1;
    @(posedge duv_if.cb.tx_stb_o);
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg + 1);
    @(posedge duv_if.cb.tx_stb_o);
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg + 0);
    @(posedge duv_if.cb.tx_stb_o);
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg - 1);



    // TODO
    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
