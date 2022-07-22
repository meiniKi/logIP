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
 * file: syncro.sv
 * usage: Synchronizer of async signals by two FFs.
 */

`default_nettype wire
module syncro #(
  parameter WIDTH = 32,                 //! signal width
  parameter INIT_VAL = 'b0              //! initial value
) (
  input  logic              clk_i,      //! system clock 
  input  logic              rst_in,     //! system reset, low active
  input  logic [WIDTH-1:0]  async_i,    //! asynchronous input
  output logic [WIDTH-1:0]  sync_o      //! synchronized output
);

  logic [WIDTH-1:0] inter;

  always_ff @(posedge clk_i) begin
    if (rst_in == 'b0) begin
      inter   <= INIT_VAL;
      sync_o  <= INIT_VAL;
    end else begin
      inter   <= async_i;
      sync_o  <= inter;
    end
  end

endmodule