/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define BUS_BIT_DELAY #(CLK_PERIOD_HALF*DS)

program sampler_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam    SYS_F       = 10_000_000;
  localparam    BAUD_RATE   = 2_000_000;

  localparam    DS          = 2*(SYS_F / BAUD_RATE);

  // Counter variable for input data
  logic [31:0]  data_i      = '0;

  // Stores the value for the expacted sample output
  logic [31:0]  exp_smpl_o  = '0;

  initial begin
    // Upcounting input signal
    forever begin
      #(CLK_PERIOD_HALF*2) duv_if.cb.data_i <= data_i;
      data_i <= data_i + 1;
    end
  end

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    // Test asserts
    `BUS_BIT_DELAY duv_if.cb.fdiv_i <= 'd8;
    duv_if.cb.set_div_i <= 'b1;
    `BUS_BIT_DELAY duv_if.cb.set_div_i <= 'b0;

    // Wait for first strobe
    @(posedge duv_if.cb.stb_o);
    exp_smpl_o = duv_if.cb.smpls_o;
    repeat (10) begin
      exp_smpl_o <= exp_smpl_o + 8;
      @(posedge duv_if.cb.stb_o);
      `SCORE_ASSERT(duv_if.cb.smpls_o == exp_smpl_o);
    end

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
