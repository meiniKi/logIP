/* Copyright (C) 2021-2022 Meinhard Kissich
 * Copyright (C) 2021-2022 Klaus Weinbauer
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
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