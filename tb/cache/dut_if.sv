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

  logic         clk_i;
  logic         rst_in;
  logic         cfg_stb_i;
  logic [3:0]   cfg_i;
  logic         stb_i;
  logic [31:0]  d_i;
  logic         stb_o;
  logic [31:0]  q_o;
  
  modport duv ( input   clk_i,
                        rst_in,
                        cfg_stb_i,
                        cfg_i,
                        stb_i,
                        d_i,
                output  stb_o,
                        q_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output clk_i;
    output rst_in;
    output cfg_stb_i;
    output cfg_i;
    output stb_i;
    output d_i;
    input  stb_o;
    input  q_o;
  endclocking

  modport tb (clocking cb);
endinterface