/*
 * file: dut_if.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

//
interface dut_if ( input logic clk_i,
                   input logic rst_in);
  //
  import tb_pkg::*;

  logic         stb_i;
  logic [31:0]  data_i;
  logic         rdy_o;
  logic         tx_o;
  logic         xstb_i;
  logic         xon_i;
  logic         xoff_i;

  modport duv (input  clk_i,
                      rst_in,
                      stb_i,
                      data_i,
                      xstb_i,
                      xon_i,
                      xoff_i,
               output rdy_o,
                      tx_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output  stb_i;
    output  data_i;
    output  xstb_i;
    output  xon_i;
    output  xoff_i;
    input   rdy_o;
    input   tx_o;
  endclocking

  modport tb (clocking cb);
endinterface