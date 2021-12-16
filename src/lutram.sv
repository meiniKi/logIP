/*
 * file: lutram.sv
 * usage: Distributed RAM implementation.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module lutram #( parameter WIDTH = 32,
                 parameter DEPTH = 5) (
input  logic                      clk_i,    //! system clock
input  logic                      rst_in,   //! system reset
input  logic                      en_i,     //! enable
input  logic                      we_i,     //! write enable (read / write)
input  logic [DEPTH-1:0]          addr_i,   //! address
input  logic [WIDTH-1:0]          d_i,      //! data in
output logic [WIDTH-1:0]          d_o       //! data out
);

logic [WIDTH-1:0] r_ram [(2**DEPTH)-1:0];

// reset not used

always_ff @(posedge clk_i) begin
  if (en_i && we_i) r_ram[addr_i] <= d_i;
  if (en_i) d_o <= r_ram[addr_i];
  else      d_o <= 'b0;
end


`ifdef FORMAL
  assume property (addr_i < DEPTH);
  // TODO
`endif

endmodule