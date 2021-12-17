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
  logic [39:0]    cmd_i;
  logic           exec_i;
  logic           tx_rdy_i;
  logic           tx_stb_o;
  logic [31:0]    tx_o;

  modport duv ( input   clk_i,
                        rst_in,
                        cmd_i,
                        input_i,
                        tx_rdy_i,
                        exec_i,
                output  tx_stb_o,
                        tx_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output cmd_i;
    output input_i;
    output tx_rdy_i;
    output exec_i;
    input  tx_stb_o;
    input  tx_o;
  endclocking

  modport tb (clocking cb);
endinterface