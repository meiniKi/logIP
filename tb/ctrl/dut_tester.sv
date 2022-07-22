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
`define CLK_DELAY `WAIT_CYCLES(1, clk_i)
`define SMPL_DELAY `WAIT_CYCLES(4, clk_i)

program ctrl_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  logic [31:0] smpls_i        = 'b0;
  logic [31:0] smpl_trg;

  initial begin
    // Upcounting input signal
    forever begin
      `SMPL_DELAY duv_if.cb.stb_i  <= 'b1;
      `CLK_DELAY  duv_if.cb.stb_i  <= 'b0;
      smpls_i <= smpls_i + 1;
    end
  end

  initial begin
    $display("----- Started ------");

    duv_if.cb.tx_rdy_i          <= 'b1;

    #(CLK_PERIOD_HALF*20)

    // Configure controller
    `CLK_DELAY  
    duv_if.cb.cmd_i             <= 'h00020004;
    duv_if.cb.set_cnt_i         <= 'b1;
    `CLK_DELAY
    duv_if.cb.set_cnt_i         <= 'b0;

    `WAIT_CYCLES(8, clk_i);
    duv_if.cb.run_i             <= 'b1;
    smpl_trg                    <= smpls_i;
    `CLK_DELAY duv_if.cb.run_i  <= 'b0;

    /* TODO: first discuss architecture
     *
    @(posedge duv_if.cb.tx_stb_o);
    duv_if.cb.tx_rdy_i          <= 'b0;
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg + 2);
    `WAIT_CYCLES(4, clk_i);
    duv_if.cb.tx_rdy_i          <= 'b1;
    @(posedge duv_if.cb.tx_stb_o);
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg + 1);
    @(posedge duv_if.cb.tx_stb_o);
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg + 0);
    @(posedge duv_if.cb.tx_stb_o);
    `SCORE_ASSERT(duv_if.cb.tx_o == smpl_trg - 1);
    */

    // TODO
    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
