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
    $timeformat(-9, 2, " ns", 10);
    $display("----- Started ------");

    duv_if.cb.smpls_i     <= 'h00000000;
    duv_if.cb.cmd_i       <= 'h00000001;
    duv_if.cb.arm_i       <= 'b0;
    duv_if.cb.set_mask_i  <= 'b0;
    duv_if.cb.set_val_i   <= 'b0;
    duv_if.cb.set_cfg_i   <= 'b0;
    duv_if.cb.stb_i       <= 'b0;
    duv_if.cb.lvl_i       <= 'b0;

    `WAIT_CYCLES(10, clk_i)

    // ##### Test arm and trigger #####
    // Configuration
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_mask_i  <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_mask_i  <= 'b0;
                            duv_if.cb.cmd_i       <= 'hFFFFFFFF;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_val_i   <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_val_i   <= 'b0;
                            duv_if.cb.cmd_i       <= 'h00000000;

    // Match when not armed and not active
                            duv_if.cb.smpls_i     <= 'h00000001;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i       <= 'b1;
    `WAIT_CYCLES(1, clk_i)  `ASSERT_EQ('b0, duv_if.cb.run_o);
                            `ASSERT_EQ('b0, duv_if.cb.match_o);
                            duv_if.cb.stb_i       <= 'b0;

    // Match when armed but not active
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b0;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  `ASSERT_EQ('b0, duv_if.cb.run_o);
                            `ASSERT_EQ('b1, duv_if.cb.match_o);
                            duv_if.cb.stb_i <= 'b0;

    // Activate stage
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.cmd_i     <= 'h00000008;
                            duv_if.cb.set_cfg_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_cfg_i <= 'b0;

    // Match when armed and active
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b0;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  `ASSERT_EQ('b1, duv_if.cb.run_o);
                            `ASSERT_EQ('b1, duv_if.cb.match_o);
                            duv_if.cb.stb_i <= 'b0;

    // Configure level
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.cmd_i     <= 'h00000100;
                            duv_if.cb.set_cfg_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_cfg_i <= 'b0;

    // Match when armed and active but not at level
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b0;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  `ASSERT_EQ('b0, duv_if.cb.match_o);
                            duv_if.cb.stb_i <= 'b0;
                            duv_if.cb.lvl_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  `ASSERT_EQ('b1, duv_if.cb.match_o);
                            duv_if.cb.stb_i <= 'b0;

    // Configure delay
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.cmd_i     <= 'h02000000;
                            duv_if.cb.set_cfg_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.set_cfg_i <= 'b0;
    
    // Match to check delay
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.arm_i <= 'b0;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  `ASSERT_EQ('b0, duv_if.cb.match_o);
                            duv_if.cb.stb_i <= 'b0;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b1;
    `WAIT_CYCLES(1, clk_i)  duv_if.cb.stb_i <= 'b0;
    @(posedge duv_if.cb.match_o) `ASSERT_EQ('b1, duv_if.cb.match_o);                    
                            

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
