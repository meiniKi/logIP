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
  output logic [WIDTH-1:0]          q_o       //! data out
);

import logIP_pkg::*;

`ifdef USE_B_RAM

  blk_mem_gen_0 i_blk_mem_gen (
    .clka   (clk_i),
    .ena    (en_i),
    .wea    (we_i),
    .addra  (addr_i),
    .dina   (d_i),
    .douta  (q_o)
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
    .q_o    (q_o)
  );

`else
  $error("No RAM selected. Use either LUT-RAM or BRAM");
`endif

endmodule