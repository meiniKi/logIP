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
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define BUS_BIT_DELAY #(CLK_PERIOD_HALF*DS)

program sampler_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam    SYS_F       = 10_000_000;
  localparam    BAUD_RATE   = 2_000_000;

  localparam    DS          = 2*(SYS_F / BAUD_RATE);

  // Counter variable for input data
  logic [31:0]  data_i      = '0;

  // Stores the value for the expacted sample output
  logic [31:0]  exp_smpl_o  = '0;

  initial begin
    // Upcounting input signal
    forever begin
      #(CLK_PERIOD_HALF*2) duv_if.cb.data_i <= data_i;
      data_i <= data_i + 1;
    end
  end

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    // Test asserts
    `BUS_BIT_DELAY duv_if.cb.fdiv_i <= 'h000007;
    duv_if.cb.set_div_i <= 'b1;
    `BUS_BIT_DELAY duv_if.cb.set_div_i <= 'b0;

    // Wait for first strobe
    @(posedge duv_if.cb.stb_o);
    exp_smpl_o = duv_if.cb.smpls_o;
    repeat (10) begin
      exp_smpl_o <= exp_smpl_o + 8;
      @(posedge duv_if.cb.stb_o);
      `SCORE_ASSERT(duv_if.cb.smpls_o == exp_smpl_o);
    end

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
