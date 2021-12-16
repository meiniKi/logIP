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
   
  logic            wrt_i;   
  logic            read_i;  
  logic [31:0]     d_i;       
  logic [31:0]     q_o;

  modport duv ( input   clk_i,
                        rst_in,  
                        wrt_i,  
                        read_i, 
                        d_i,      
                output  q_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
            output wrt_i;   
            output read_i;  
            output d_i;       
            input  q_o;
  endclocking

  modport tb (clocking cb);
endinterface