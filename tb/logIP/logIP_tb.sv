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
 * file: logIP_tb.sv
 * usage: Testbench for logIP.sv
 * 
 */

`include "declarations.svh"
`include "uart8.svh"
`default_nettype wire
`timescale 1ns/1ps

module logIP_tb;
  import tb_pkg::*;

  logic clk_i  = 0;
  logic rst_in = 0;

  Scoreboard      i_scoreboard;
  Client          i_client;
  Uart8           i_uart8;
  score_mbox_t    mbx;       

  initial begin
    // Dump
    $dumpfile("logIP_tb.vcd");
    $dumpvars(5, duv_wrapper);

    // Reset            
    #(10*CLK_PERIOD_HALF) rst_in = 0;
    #(2*CLK_PERIOD_HALF)  rst_in = 1;
  end

  always begin : clock_gen
    #(CLK_PERIOD_HALF) clk_i = 1;
    #(CLK_PERIOD_HALF) clk_i = 0;
  end

  dut_if duv_if (clk_i, rst_in);
  dut_wrapper duv_wrapper (duv_if.duv);
  logIP_tester duv_tester(duv_if.tb, clk_i, mbx, i_client);

  initial begin
    mbx = new();
    i_scoreboard  = new (mbx);
    i_uart8       = new (20); 
    i_client      = new (i_uart8);

    fork
      i_scoreboard.run();
      i_uart8.run_transmitter(duv_if.rx_i);
      i_uart8.run_receiver(duv_if.tx_o);
      // append
    join
  end

endmodule



