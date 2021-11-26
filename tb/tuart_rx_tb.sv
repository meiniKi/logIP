/*
 * file: tuart_rx_tb.sv
 * usage: Testbench for tuart_rx_tb.sv
 * 
 */

`default_nettype wire

`timescale 1ns/1ps

//
interface dut_if ( input logic clk_i,
                   input logic rst_in );
  //
  import tb_pkg::*;

  logic         rx_sync_i;
  logic [31:0]  data_o;
  logic         rdy_o;

  modport duv (input  clk_i,
                      rst_in,
                      rx_sync_i,
              output  data_o,
                      rdy_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output rx_sync_i;
    input  data_o;
    input  rdy_o;
  endclocking

  modport tb (clocking cb);
endinterface


 //
`timescale 1ns/1ps
module dut_wrapper(dut_if.duv ifc);
  tuart_rx dut(
                .clk_i      (ifc.clk_i),
                .rst_in     (ifc.rst_in),
                .rx_sync_i  (ifc.rx_sync_i),
                .data_o     (ifc.data_o),
                .rdy_o      (ifc.rdy_o));
endmodule

//
`timescale 1ns/1ps
module tuart_rx_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;

  initial begin
    // Dump
    $dumpfile("tuart_rx_tb.vcd");
    $dumpvars(3, duv_wrapper);
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  dut_if duv_if (clk_i, rst_in);
  dut_wrapper duv_wrapper (duv_if.duv);
  uart_rx_tester duv_tester(duv_if.tb, clk_i);

endmodule


//
`timescale 1ns/1ps
program uart_rx_tester ( dut_if.tb duv_if, input clk_i );

  initial begin
    $display("----- Started ------");
    ##1 duv_if.cb.rx_sync_i <= 1;
    ##2 duv_if.cb.rx_sync_i <= 0;
    ##2 duv_if.cb.rx_sync_i <= 1;
    ##2 duv_if.cb.rx_sync_i <= 1;
    duv_if.cb.rx_sync_i <= 1;
    $display("----- Done ------");
    #50 $finish;
  end

endprogram



