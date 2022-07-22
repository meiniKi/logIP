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
 * file: tuart_tx_tb.sv
 * usage: Testbench for tuart_tx_tb.sv
 * 
 */

`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

module tuart_tx_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;

  Scoreboard      i_scoreboard;
  score_mbox_t    mbx;    

  initial begin
    // Dump
    $dumpfile("tuart_tx_tb.vcd");
    $dumpvars(5, duv_wrapper);

    // Reset            
    `WAIT_CYCLES(2, clk_i)  rst_in = 0;
    `WAIT_CYCLES(2, clk_i)  rst_in = 1;
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  dut_if duv_if (clk_i, rst_in);
  dut_wrapper duv_wrapper (duv_if);
  uart_tx_tester duv_tester (duv_if, clk_i, mbx);

  initial begin
    mbx = new();
    i_scoreboard = new (mbx);

    fork
      i_scoreboard.run();
      // append
    join
  end

endmodule



