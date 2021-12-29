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

  logic [31:0]    input_i;
  logic [31:0]    cmd_i;
  logic [ 7:0]    opc_i;
  logic           exec_i;
  logic           we_o;
  logic           addr_o;
  logic [31:0]    mem_i;
  logic [31:0]    mem_o;
  logic           tx_rdy_i;
  logic           tx_stb_o;
  logic [31:0]    tx_o;
  logic           tx_xon_o;
  logic           tx_xoff_o;

  modport duv ( input   clk_i,
                        rst_in,
                        cmd_i,
                        opc_i,
                        input_i,
                        tx_rdy_i,
                        exec_i,
                        mem_i,
                output  we_o,
                        addr_o,
                        tx_stb_o,
                        mem_o,
                        tx_o,
                        tx_xon_o,
                        tx_xoff_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output cmd_i;
    output opc_i;
    output input_i;
    output tx_rdy_i;
    output exec_i;
    input  tx_stb_o;
    input  tx_o;
    input  tx_xon_o;
    input  tx_xoff_o;
    input  we_o;
    input  addr_o;
    input  mem_o;
    output mem_i;
  endclocking

  modport tb (clocking cb);
endinterface