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

  logic         rx_i = '1;
  logic [39:0]  data_o;
  logic         stb_o;

  modport duv (input  clk_i,
                      rst_in,
                      rx_i,
              output  data_o,
                      stb_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output rx_i;
    input  data_o;
    input  stb_o;
  endclocking

  modport tb (clocking cb);
endinterface