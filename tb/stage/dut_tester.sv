/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

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

    `WAIT_CYLCES(10, clk_i)

    // ##### Test arm and trigger #####
    // Configuration
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.set_mask_i <= 'b1;
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.set_mask_i <= 'b0;
                            duv_if.cb.cmd_i <= 'hFFFFFFFF;
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.set_val_i <= 'b1;
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.set_val_i <= 'b0;
                            duv_if.cb.cmd_i <= 'h00000000;

    // Match when not armed
    duv_if.cb.smpls_i <= 'h00000001;
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYLCES(1, clk_i)  `SCORE_ASSERT(duv_if.cb.run_o == 'b0);
                            duv_if.cb.stb_i <= 'b0;
    // Match when armed
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.arm_i <= 'b1;
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.arm_i <= 'b0;
    `WAIT_CYLCES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYLCES(1, clk_i) `SCORE_ASSERT(duv_if.cb.run_o == 'b1);
                            duv_if.cb.stb_i <= 'b0;

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
