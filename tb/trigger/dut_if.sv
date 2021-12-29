/*
 * file: dut_if.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

//
interface dut_if ( input logic clk_i );
  //
  import tb_pkg::*;
 
  logic [31:0]      cmd_i;
  logic             set_mask_i;              
  logic             set_val_i;
  logic             set_cfg_i;
  logic [1:0]       stg_i;
  logic             arm_i;
  logic             stb_i;
  logic [31:0]      smpls_i;
  logic             run_o;
  logic             rst_in;
  logic             exec_i;

  modport duv ( input   clk_i,
                        rst_in,
                        cmd_i,     
                        set_mask_i,
                        set_val_i, 
                        set_cfg_i,
                        exec_i,
                        stg_i,
                        arm_i,     
                        stb_i,     
                        smpls_i,  
                output  run_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output cmd_i;     
    output set_mask_i;
    output set_val_i; 
    output set_cfg_i; 
    output stg_i;
    output arm_i;     
    output stb_i;     
    output smpls_i; 
    output rst_in;
    output exec_i;
    input  run_o;
  endclocking

  modport tb (clocking cb);
endinterface