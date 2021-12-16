/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY `WAIT_CYCLES(1, clk_i)

program trigger_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");

    duv_if.cb.smpls_i     <= 'h00000000;
    duv_if.cb.arm_i       <= 'b0;
    duv_if.cb.set_mask_i  <= 'b0;
    duv_if.cb.set_val_i   <= 'b0;
    duv_if.cb.set_cfg_i   <= 'b0;
    duv_if.cb.stb_i       <= 'b0;

    `WAIT_CYCLES(10, clk_i)

    // Configuration stage 0
                duv_if.cb.cmd_i       <= 'h00000001;
                duv_if.cb.stg_i       <= 'b0;
                duv_if.cb.set_mask_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.set_mask_i  <= 'b0;
                duv_if.cb.cmd_i       <= 'hFFFFFFFF;
                duv_if.cb.set_val_i   <= 'b1;
    `CLK_DELAY  duv_if.cb.set_val_i   <= 'b0;

    // Configuration stage 1
                duv_if.cb.cmd_i       <= 'h00000001;
                duv_if.cb.stg_i       <= 'b1;
                duv_if.cb.set_mask_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.set_mask_i  <= 'b0;
                duv_if.cb.cmd_i       <= 'hFFFFFFFF;
                duv_if.cb.set_val_i   <= 'b1;
    `CLK_DELAY  duv_if.cb.set_val_i   <= 'b0;
                duv_if.cb.cmd_i       <= 'h00000108; // set lvl = 1 and start = 1
                duv_if.cb.set_cfg_i   <= 'b1;
    `CLK_DELAY  duv_if.cb.set_cfg_i   <= 'b0;

    // ##### TEST #####
    `CLK_DELAY  duv_if.cb.smpls_i     <= 'h00000001;
    `CLK_DELAY  duv_if.cb.arm_i       <= 'b1;
    `CLK_DELAY  duv_if.cb.arm_i       <= 'b0;
                duv_if.cb.stb_i       <= 'b1;
                `SCORE_ASSERT(duv_if.cb.run_o == 'b0);
    `CLK_DELAY  `SCORE_ASSERT(duv_if.cb.run_o == 'b0);
    `CLK_DELAY  `SCORE_ASSERT(duv_if.cb.run_o == 'b0);
                duv_if.cb.stb_i       <= 'b0;
    `CLK_DELAY  `SCORE_ASSERT(duv_if.cb.run_o == 'b0);
    `CLK_DELAY  duv_if.cb.stb_i       <= 'b1;
    `CLK_DELAY  `SCORE_ASSERT(duv_if.cb.run_o == 'b1);

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
