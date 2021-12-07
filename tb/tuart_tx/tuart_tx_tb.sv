/*
 * file: tuart_tx_tb.sv
 * usage: Testbench for tuart_tx_tb.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module tuart_tx_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;


  initial begin
    // Dump
    $dumpfile("tuart_tx_tb.vcd");
    $dumpvars(5, duv_wrapper);

    // Reset            
    #(10*CLK_PERIOD_HALF) rst_in = 0;
    #(2*CLK_PERIOD_HALF)  rst_in = 1;
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  FlowCtr xctrl_i ();
  dut_if duv_if (clk_i, rst_in, xctrl_i);
  dut_wrapper duv_wrapper (duv_if);
  uart_tx_tester duv_tester(duv_if, clk_i);

endmodule



