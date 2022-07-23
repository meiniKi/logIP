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

  logic         set_cnt_i;
  logic [31:0]  cmd_i;
  logic         run_i;
  logic         stb_i;
  logic         tx_rdy_i;
  logic         tx_stb_o;
  logic         tx_sel_o;
  
  modport duv (input  clk_i,
                      rst_in,
                      set_cnt_i,
                      cmd_i,
                      run_i,
                      stb_i,
                      tx_rdy_i,
                      tx_stb_o,
                      tx_sel_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output set_cnt_i;
    output cmd_i;
    output run_i;
    output stb_i;
    output tx_rdy_i;
    input  tx_stb_o;
    input  tx_sel_o;
  endclocking

  modport tb (clocking cb);
endinterface