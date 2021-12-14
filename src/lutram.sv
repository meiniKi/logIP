/*
 * file: lutram.sv
 * usage: Distributed RAM implementation.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module lutram #( parameter WIDTH = 32,
                 parameter DEPTH = 200) (
input  logic                      clk_i,    //! system clock
input  logic                      rst_in,   //! system reset
input  logic                      en_i,     //! enable
input  logic                      we_i,     //! write enable (read / write)
input  logic [$clog2(DEPTH)-1:0]  addr_i,   //! address
input  logic [WIDTH-1:0]          d_i,      //! data in
output logic [WIDTH-1:0]          q_o       //! data out
);

logic [WIDTH-1:0] r_ram [(2**DEPTH)-1:0];

always_ff @(posedge clk) begin
  // reset omitted to decrease area
  if (we_a)
    r_ram[addr_a] <= d_i;
  q_o <= r_ram[addr_i];
end

endmodule