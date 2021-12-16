/*
 * file: mmu.sv
 * usage: Memory management unit for RAM management
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module mmu #( parameter WIDTH = 32,
              parameter DEPTH = 5) (
  input  logic                      clk_i,        //! system clock
  input  logic                      rst_in,       //! system reset
  input  logic                      wrt_i,        //! write
  input  logic                      read_i,       //! read
  input  logic [WIDTH-1:0]          d_i,          //! data in
  output logic [WIDTH-1:0]          d_o           //! data out
);

import logIP_pkg::*;

  logic             en = 'b1;
  
  logic [DEPTH-1:0] ptr;
  logic [DEPTH-1:0] ptr_next;

  ramif #(  .WIDTH (WIDTH),
            .DEPTH (DEPTH)) i_ramif (
    .clk_i  (clk_i),
    .rst_in (rst_in),
    .en_i   (en),
    .we_i   (wrt_i),
    .addr_i (ptr),
    .d_i    (d_i),
    .d_o    (d_o)
  );

  assign ptr_next =   wrt_i ==  'b1 ? ptr_next <= ptr + 1 :
                      read_i == 'b1 ? ptr_next <= ptr - 1 
                                    : ptr_next <= ptr;

  always_ff @(posedge clk_i) begin : fsm
    if (~rst_in) begin
      ptr   <= 'b0;
    end else begin
      ptr   <= ptr_next;
    end
  end

endmodule