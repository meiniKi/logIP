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
   
  logic            mem_wrt_i;   
  logic            mem_read_i;  
  logic [31:0]     mem_i;       
  logic [31:0]     mem_o;

  modport duv ( input   clk_i,
                        rst_in,  
                        mem_wrt_i,  
                        mem_read_i, 
                        mem_i,      
                output  mem_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
            output mem_wrt_i;   
            output mem_read_i;  
            output mem_i;       
            input  mem_o;
  endclocking

  modport tb (clocking cb);
endinterface