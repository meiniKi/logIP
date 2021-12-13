/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define BUS_BIT_DELAY #(CLK_PERIOD_HALF*DS)

program indec_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    // Test run command (short)
    `BUS_BIT_DELAY duv_if.cb.opc_i <= 'h01;
    duv_if.cb.stb_i <= 'b1;
    @(posedge duv_if.cb.stb_o);
    `SCORE_ASSERT(duv_if.cb.arm_o == 'b1);    
    duv_if.cb.stb_i <= 'b0;

    // Test set trigger mask command (long)
    `BUS_BIT_DELAY duv_if.cb.opc_i <= 'b1100??00;
    //duf_if.cb.cmd_i <= 'h11223344;
    duv_if.cb.stb_i <= 'b1;
    @(posedge duv_if.cb.stb_o);
    `SCORE_ASSERT(duv_if.cb.set_mask_o == 'b1);    
    duv_if.cb.stb_i <= 'b0;

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
