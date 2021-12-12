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

  input  logic [23:0]     fdiv_i;
  input  logic            set_div_i;
  input  logic [31:0]     data_i;
  output logic [31:0]     smpls_o;
  output logic            stb_o;

  modport duv ( input   clk_i,
                        rst_in,
                        fdiv_i,
                        set_div_i,
                        data_i,
                output  smpls_o,
                        stb_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output    fdiv_i;
    output    set_div_i;
    input     smpls_o;
    input     stb_o;
  endclocking

  modport tb (clocking cb);
endinterface