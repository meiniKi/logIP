/*
 * file: dut_if.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

//
interface dut_if ( input logic clk_i,
                  input logic rst_in );
  //
  import tb_pkg::*;

  logic         rx_async_i = '1;
  logic [39:0]  data_o;
  logic         rdy_o;

  modport duv (input  clk_i,
                      rst_in,
                      rx_async_i,
              output  data_o,
                      rdy_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output rx_async_i;
    input  data_o;
    input  rdy_o;
  endclocking

  modport tb (clocking cb);
endinterface