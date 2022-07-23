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

program indec_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    // Test run command (short)
    `BUS_BIT_DELAY duv_if.cb.opc_i <= 'h01;
    duv_if.cb.stb_i <= 'b1;
    @(posedge clk_i);
    `SCORE_ASSERT(duv_if.cb.arm_o == 'b1);    
    duv_if.cb.stb_i <= 'b0;

    // Test set trigger mask command (long)
    `BUS_BIT_DELAY duv_if.cb.opc_i <= 'b1100??00;
    duv_if.cb.stb_i <= 'b1;
    @(posedge clk_i);
    `SCORE_ASSERT(duv_if.cb.set_mask_o == 'b1);    
    duv_if.cb.stb_i <= 'b0;

    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
