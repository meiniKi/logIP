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
 * file: dut_if.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

//
interface dut_if ( input logic clk_i,
                   input logic rst_in);
  //
  import tb_pkg::*;

  logic         stb_i;
  logic [31:0]  data_i;
  logic         rdy_o;
  logic         tx_o;
  logic         xstb_i;
  logic         xon_i;
  logic         xoff_i;
  logic [2:0]   sel_i;

  modport duv (input  clk_i,
                      rst_in,
                      stb_i,
                      data_i,
                      xstb_i,
                      xon_i,
                      xoff_i,
                      sel_i,
               output rdy_o,
                      tx_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output  stb_i;
    output  data_i;
    output  xstb_i;
    output  xon_i;
    output  xoff_i;
    output  sel_i;
    input   rdy_o;
    input   tx_o;
  endclocking

  modport tb (clocking cb);
endinterface