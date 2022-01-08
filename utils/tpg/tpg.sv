/*
 * file: tpg.sv
 * usage: Simple test pattern generator
 *
 */

`default_nettype wire
`timescale 1ns/1ps
module tpg #(parameter CHLS = 32)(
  // General
  input  logic            clk_i,          //! system clock
  input  logic            rst_in,         //! system reset, low active
  // Output
  output logic [CHLS-1:0] chls            //! output test pattern
);

  logic [CHLS:0] cnt;

  for (genvar i = 0; i < CHLS; i++) begin
    assign chls[i]  = cnt[i];
  end

  always_ff @(posedge clk_i) begin
    if (~rst_in) begin
      cnt <= 'b0;
    end else begin
      cnt <= cnt + 'b1;
    end
  end

endmodule