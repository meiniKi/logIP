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

  logic           stb_i;
  logic [ 7:0]    opc_i;
 
  logic           sft_rst_o;
  logic           arm_o;
  logic           id_o;
  logic           set_mask_o;
  logic           set_val_o;
  logic           set_cfg_o;
  logic           set_div_o;
  logic           set_cnt_o;
  logic           set_flgs_o;
  logic [ 1:0]    stg_o;

  logic           xon_o;
  logic           xoff_o;
 
  logic           rd_meta_o;
  logic           fin_now_o;
  logic           rd_inp_o;
  logic           arm_adv_o;
  logic           set_adv_cfg_o;
  logic           set_adv_dat_o;

  modport duv ( input   clk_i,
                        rst_in,
                        stb_i,
                        opc_i,
                output  sft_rst_o,
                        arm_o,
                        id_o,
                        set_mask_o,
                        set_val_o,
                        set_cfg_o,
                        set_div_o,
                        set_cnt_o,
                        set_flgs_o,
                        stg_o,
                        rd_meta_o,
                        fin_now_o,
                        rd_inp_o,
                        arm_adv_o,
                        set_adv_cfg_o,
                        set_adv_dat_o,
                        xon_o,
                        xoff_o);

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output    stb_i;
    output    opc_i;
    input     sft_rst_o;
    input     arm_o;
    input     id_o;
    input     set_mask_o;
    input     set_val_o;
    input     set_cfg_o;
    input     set_div_o;
    input     set_cnt_o;
    input     set_flgs_o;
    input     stg_o;
    input     rd_meta_o;
    input     fin_now_o;
    input     rd_inp_o;
    input     arm_adv_o;
    input     set_adv_cfg_o;
    input     set_adv_dat_o;
    input     xon_o;
    input     xoff_o;
  endclocking

  modport tb (clocking cb);
endinterface