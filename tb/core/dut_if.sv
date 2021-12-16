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

  logic [31:0]    cmd_i;
  logic [31:0]    input_i;
  logic           tx_rdy_i;
  logic [31:0]    mem_i;
  logic           we_o;
  logic [4:0]     addr_o;
  logic [31:0]    mem_o;
  logic           tx_stb_o;
  logic [31:0]    tx_o;

  modport duv ( input   clk_i,
                        rst_in,
                        cmd_i,
                        input_i,
                        tx_rdy_i,
                        mem_i,
                output  we_o,
                        addr_o,
                        mem_o,
                        tx_stb_o,
                        tx_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    input  cmd_i;
    input  input_i;
    input  tx_rdy_i;
    input  mem_i;
    output we_o;
    output addr_o;
    output mem_o;
    output tx_stb_o;
    output tx_o;
  endclocking

  modport tb (clocking cb);
endinterface