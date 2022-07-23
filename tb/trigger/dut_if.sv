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
interface dut_if ( input logic clk_i );
  //
  import tb_pkg::*;
 
  logic [31:0]      cmd_i;
  logic             set_mask_i;              
  logic             set_val_i;
  logic             set_cfg_i;
  logic [1:0]       stg_i;
  logic             arm_i;
  logic             stb_i;
  logic [31:0]      smpls_i;
  logic             run_o;
  logic             rst_in;

  modport duv ( input   clk_i,
                        rst_in,
                        cmd_i,     
                        set_mask_i,
                        set_val_i, 
                        set_cfg_i,
                        stg_i,
                        arm_i,     
                        stb_i,     
                        smpls_i,  
                output  run_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output cmd_i;     
    output set_mask_i;
    output set_val_i; 
    output set_cfg_i; 
    output stg_i;
    output arm_i;     
    output stb_i;     
    output smpls_i; 
    output rst_in;
    input  run_o;
  endclocking

  modport tb (clocking cb);
endinterface