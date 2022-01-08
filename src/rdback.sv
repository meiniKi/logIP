/*
 * file: rdback.sv
 * usage:
 *
 * Without OLS extensions, the readback only provides the device's ID.
 * When OLS instructions are supported, the client can read back parameters
 * that span over multiple words. As the read-back and the transmission of 
 * samples are disjunct phases, the FSMs are split (ctrl vs. rdback).
 */

`default_nettype wire
`timescale 1ns/1ps

module rdback (
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  input  logic                  exec_i,     //! execute command
  input  logic                  tx_rdy_i,   //! transceiver is ready
  // Select readback data
  input  logic                  id_i,       //! flag to read back id
  //input  logic                  rd_meta_i   // Not yet used
  output logic [31:0]           tx_o,       //! transmit data output
  output logic                  stb_o       //! strobe transmit 
);

// Most of the control signals can be ignored until OLS
// instructions are supported.
assign tx_o   = "SLA1";
assign stb_o  = exec_i & id_i;

endmodule