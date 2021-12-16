/*
 * file: ramif.sv
 * usage: RAM interface to instantiate either
 *        distributed (lut) RAM or BRAM
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module ramif #( parameter WIDTH = 32,
                parameter DEPTH = 5) (
  input  logic                      clk_i,    //! system clock
  input  logic                      rst_in,   //! system reset
  input  logic                      en_i,     //! enable
  input  logic                      we_i,     //! write enable (read / write)
  input  logic [DEPTH-1:0]          addr_i,   //! address
  input  logic [WIDTH-1:0]          d_i,      //! data in
  output logic [WIDTH-1:0]          d_o       //! data out
);

import logIP_pkg::*;

`ifdef USE_B_RAM

  blk_mem_gen_0 i_blk_mem_gen (
    .clka   (clk_i),
    .ena    (en_i),
    .wea    (we_i),
    .addra  (addr_i),
    .dina   (d_i),
    .douta  (d_o)
  );

`elsif USE_LUT_RAM

  lutram #( .WIDTH (WIDTH),
            .DEPTH (DEPTH)) i_lutram (
    .clk_i  (clk_i),
    .rst_in (rst_in),
    .en_i   (en_i),
    .we_i   (we_i),
    .addr_i (addr_i),
    .d_i    (d_i),
    .d_o    (d_o)
  );

`else
  $error("No RAM selected. Use either LUT-RAM or BRAM");
`endif

endmodule