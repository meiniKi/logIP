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
 * file: lutram.sv
 * usage: Distributed RAM implementation.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module lutram #( parameter WIDTH = 32,
                 parameter DEPTH = 3) (
input  logic                      clk_i,    //! system clock
input  logic                      rst_in,   //! system reset
input  logic                      en_i,     //! enable
input  logic                      we_i,     //! write enable (read / write)
input  logic [DEPTH-1:0]          addr_i,   //! address
input  logic [WIDTH-1:0]          d_i,      //! data in
output logic [WIDTH-1:0]          q_o       //! data out
);

logic [WIDTH-1:0] r_ram [(2**DEPTH)-1:0];

// reset not used

assign q_o = en_i ? r_ram[addr_i] : 'b0;

always_ff @(posedge clk_i) begin
  if (en_i && we_i) r_ram[addr_i] <= d_i;
end


`ifdef FORMAL
  default clocking @(posedge clk_i); endclocking
	default disable iff (~rst_in);

  logic f_pre_init = 0;
  logic f_init = 0;
  always_ff @(posedge clk_i) begin : f_initial_reset
    if (!f_init) begin
      if (!f_pre_init)  f_pre_init  <= 1;
      else              f_init      <= 1;
    end
  end

  asme_rst:   assume property (f_init == 'b0 |-> rst_in == 'b0);
  asme_we:    assume property (f_init == 'b0 |-> we_i == 'b0);

  asrt_n_en:  assert property ( (~en_i) |-> (q_o == 'b0) );
  asrt_n_we:  assert property ( ~we_i   |=> (r_ram == $past(r_ram)) );
  asrt_we:    assert property ( we_i && en_i |=> (r_ram[$past(addr_i)] == $past(d_i)) );
  asrt_rd:    assert property ( en_i |-> (q_o == r_ram[addr_i]));

`endif

endmodule