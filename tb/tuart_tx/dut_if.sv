/*
 * file: dut_if.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

//
interface dut_if ( input logic clk_i,
                   input logic rst_in,
                   FlowCtr xctrl_i);
  //
  import tb_pkg::*;

  logic         stb_i;
  logic [31:0]  data_i;
  logic         rdy_o;
  logic         tx_o;

  //
  // Seems that interfaces cannot be nested.
  // Thus, _modports_ are not used here for the tb.
  //

endinterface