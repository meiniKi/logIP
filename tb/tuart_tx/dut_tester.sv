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
`define BUS_BIT_DELAY       #(CLK_PERIOD_HALF*DS)
`define BUS_BIT_DELAY_HALF  #(CLK_PERIOD_HALF*DS/2)

program uart_tx_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  logic [31:0] data_1 = 'hFFFF0000;
  logic [31:0] data_2 = 'hAAAAAAAA;

  task waitTx();
    $write("[INFO] Waiting for negedge on tx signal... ");
    @(negedge duv_if.cb.tx_o);
    $display("DONE");
  endtask

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    duv_if.stb_i    <= 'b0;
    duv_if.data_i   <= 'b0;
    duv_if.xstb_i   <= 'b0;
    duv_if.xoff_i   <= 'b0;
    duv_if.xon_i    <= 'b0;
    duv_if.sel_i    <= 'd4;

    #(10 * CLK_PERIOD_HALF*DS)

    // ##### Test data direction #####
    `BUS_BIT_DELAY 
    duv_if.data_i   <= data_1;
    duv_if.stb_i    <= 'b1;

    repeat(2) begin
      waitTx();
      `BUS_BIT_DELAY_HALF `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);         // Start bit
      repeat(8) begin
        `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);
      end
      `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);              // Stop bit
    end

    duv_if.stb_i    <= 'b0;

    repeat(2) begin
      waitTx();
      `BUS_BIT_DELAY_HALF `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);         // Start bit
      repeat(8) begin 
        `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);
      end
      `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);              // Stop bit
    end

    @(posedge duv_if.cb.rdy_o);

    // ##### Test alternating data #####
    `BUS_BIT_DELAY 
    duv_if.data_i   <= data_2;
    duv_if.stb_i    <= 'b1;

    repeat(4) begin
      waitTx();
      `BUS_BIT_DELAY_HALF `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);         // Start bit
      repeat(4) begin
        `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);
        `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);
      end
      `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);              // Stop bit
    end

    duv_if.stb_i    <= 'b0;

    // ##### Test selection of only first byte #####
    `BUS_BIT_DELAY
    duv_if.data_i     <= 'hDDCCBBAA;
    duv_if.sel_i      <= 'b1;
    duv_if.stb_i      <= 'b1;
    waitTx();
    `BUS_BIT_DELAY_HALF `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);         // Start bit
    repeat(4) begin
      `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b0);
      `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);
    end
    `BUS_BIT_DELAY `SCORE_ASSERT(duv_if.cb.tx_o == 'b1);
    // No more bytes should be transmitted
    repeat(20) begin
      `SCORE_ASSERT_STR(duv_if.cb.tx_o == 'b1, "Transmitting to many bytes.");
    end
    duv_if.stb_i     <= 'b0;

    // ##### Test selection of only first byte #####
    `BUS_BIT_DELAY
    duv_if.data_i     <= 'hFFFFFFFF;
    duv_if.sel_i      <= 'b0;
    duv_if.stb_i      <= 'b1;
    repeat(20) begin
      `SCORE_ASSERT_STR(duv_if.cb.tx_o == 'b1, "No data should be transmitted.");
    end
    duv_if.stb_i     <= 'b0;

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
