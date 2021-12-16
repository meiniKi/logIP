/*
 * file: core.sv
 * usage: 
 *
 */

`default_nettype wire
`timescale 1ns/1ps;

module core #(
  parameter SMPL_WIDTH=32,                  //! bits of a single sample
  parameter TX_WIDTH=32,                    //! bits the transmitter can send at once
  parameter DEPTH=5                         //! memory depth / address width
) (           
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  
  input  logic [31:0]           cmd_i,      //! command data
  input  logic [SMPL_WIDTH-1:0] input_i,    //! input to sample
  input  logic                  tx_rdy_i,   //! transmitter ready flag
  input  logic [SMPL_WIDTH-1:0] mem_i,      //! input from memory
  output logic                  we_o,       //! write enable
  output logic [DEPTH-1:0]      addr_o,     //! memory address
  output logic [SMPL_WIDTH-1:0] mem_o,      //! output to memory
  output logic                  tx_stb_o,   //! starts transmitter
  output logic [TX_WIDTH-1:0]   tx_o        //! data for the transmitter to send
);




endmodule