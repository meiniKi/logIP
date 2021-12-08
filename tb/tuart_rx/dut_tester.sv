/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
program uart_rx_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    repeat (5) begin
      #(CLK_PERIOD_HALF*DS) duv_if.cb.rx_async_i <= 1;
      #(CLK_PERIOD_HALF*DS) duv_if.cb.rx_async_i <= 0;

      repeat(8) #(CLK_PERIOD_HALF*DS) duv_if.cb.rx_async_i <= 1;

      //mbx.put()

      #(CLK_PERIOD_HALF*DS)  duv_if.cb.rx_async_i <= 0;
      #(CLK_PERIOD_HALF*DS)  duv_if.cb.rx_async_i <= 1;
    end
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
