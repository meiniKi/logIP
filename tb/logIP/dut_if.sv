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

  logic [31:0]  chls_i;
  logic         rx_i;
  logic         tx_o;

  modport duv ( input   clk_i,
                        rst_in,
                        chls_i,
                        rx_i,
                output  tx_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output    chls_i;
  endclocking

  modport tb (clocking cb, output rx_i, input tx_o);
endinterface