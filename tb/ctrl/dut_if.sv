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

  logic         set_cnt_i; 
  logic [31:0]  cmd_i;     
  logic         run_i;     
  logic         stb_i;     
  logic [31:0]  smpls_i;   
  logic [31:0]  d_i;     
  logic         tx_rdy_i;  
  logic         read_o;
  logic         wrt_o; 
  logic [31:0]  d_o;     
  logic         tx_stb_o;  
  logic [31:0]  tx_o;      
  
  modport duv (input  clk_i,
                      rst_in,
                      set_cnt_i,
                      cmd_i,
                      run_i,
                      stb_i,
                      smpls_i,
                      d_i,
                      tx_rdy_i,
              output  read_o,
                      wrt_o,
                      d_o,
                      tx_stb_o,
                      tx_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output set_cnt_i;
    output cmd_i;
    output run_i;
    output stb_i;
    output smpls_i;
    output d_i;
    output tx_rdy_i;
    input  read_o;
    input  wrt_o;
    input  d_o;
    input  tx_stb_o;
    input  tx_o;
  endclocking

  modport tb (clocking cb);
endinterface