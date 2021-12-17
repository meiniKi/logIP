/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

program logIP_tester ( dut_if.tb duv_if, 
                      input clk_i, 
                      input score_mbox_t mbx,
                      input Uart8 uart);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");

    // Test run command (short)
    uart.queue('h84);


    // Test set trigger mask command (long)
    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
