/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY #(CLK_PERIOD_HALF*2)

program stage_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");

    duv_if.cb.smpls_i     <= 'h00000000;
    duv_if.cb.cmd_i       <= 'h00000001;
    duv_if.cb.arm_i       <= 'b0;
    duv_if.cb.set_mask_i  <= 'b0;
    duv_if.cb.set_val_i   <= 'b0;
    duv_if.cb.set_cfg_i   <= 'b0;
    duv_if.cb.stb_i       <= 'b0;

    #(65)

    // ##### Test arm and trigger #####
    // Configuration
    `CLK_DELAY duv_if.cb.set_mask_i <= 'b1;
    `CLK_DELAY duv_if.cb.set_mask_i <= 'b0;
    duv_if.cb.cmd_i <= 'hFFFFFFFF;
    `CLK_DELAY duv_if.cb.set_val_i <= 'b1;
    `CLK_DELAY duv_if.cb.set_val_i <= 'b0;
    duv_if.cb.cmd_i <= 'h00000000;

    // Match when not armed
    duv_if.cb.smpls_i <= 'h00000001;
    `CLK_DELAY duv_if.cb.stb_i <= 'b1;
    `CLK_DELAY `SCORE_ASSERT(duv_if.cb.run_o == 'b0);
    duv_if.cb.stb_i <= 'b0;
    // Match when armed
    `CLK_DELAY duv_if.cb.arm_i <= 'b1;
    `CLK_DELAY duv_if.cb.arm_i <= 'b0;
    `CLK_DELAY duv_if.cb.stb_i <= 'b1;
    `CLK_DELAY `SCORE_ASSERT(duv_if.cb.run_o == 'b1);
    duv_if.cb.stb_i <= 'b0;

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
