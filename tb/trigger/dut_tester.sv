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
`include "trigger_helper.svh"
`default_nettype wire
`timescale 1ns/1ps



program trigger_tester (dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");

    duv_if.cb.smpls_i     <= 'h00000000;
    duv_if.cb.arm_i       <= 'b0;
    duv_if.cb.set_mask_i  <= 'b0;
    duv_if.cb.set_val_i   <= 'b0;
    duv_if.cb.set_cfg_i   <= 'b0;
    duv_if.cb.stb_i       <= 'b0;
    duv_if.cb.rst_in      <= 'b0;

    `WAIT_CYCLES(10, clk_i)
    duv_if.cb.rst_in      <= 'b1;

    ////////////// TEST 1 //////////////
    // simple positive trigger on one channel, one stage
    //
    //               st       mask         value
    `SET_STAGE_VAL(2'd0, 32'b00000001, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd1, 32'h00000000, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd2, 32'h00000000, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd3, 32'h00000000, 32'hFFFFFFFF);

    //                stg  dly_l dly_h ch[3:0] ch[4] lvl  start  ser
    `SET_STAGE_CONFIG(2'd0, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd1, 1'd0);
    `SET_STAGE_CONFIG(2'd1, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);
    `SET_STAGE_CONFIG(2'd2, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);
    `SET_STAGE_CONFIG(2'd3, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);

    `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t0, after-config, no trigger");

    repeat (10)
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t0, after-config, no trigger loop");

    repeat (10) begin
      duv_if.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t0, after-config, strobe, not armed");
      duv_if.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t0, after-config, strobe, not armed 2");
    end

    `SET_ARMED;

    repeat (10) begin
      duv_if.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t0, after-config, strobe, no match");
      duv_if.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t0, after-config, strobe, no match 2");
    end
    
    duv_if.cb.smpls_i <= 'h1; 
    duv_if.cb.stb_i   <= 'b1;
    `CLK_DELAY 
    `CLK_DELAY
    `CLK_DELAY
    `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b1, "t0 triggered");

    `SET_RESET;
    ////////////// TEST 2 //////////////
    // simple trigger on one channel with level > 0
    // use other stage to increment level
    //
    //               st       mask         value
    `SET_STAGE_VAL(2'd0, 32'b00000001, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd1, 32'h00000002, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd2, 32'h00000000, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd3, 32'h00000000, 32'hFFFFFFFF);

    //                stg  dly_l dly_h ch[3:0] ch[4] lvl  start  ser
    `SET_STAGE_CONFIG(2'd0, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);
    `SET_STAGE_CONFIG(2'd1, 8'h0, 8'h0, 4'd0, 1'd0, 2'd1, 1'd1, 1'd0);
    `SET_STAGE_CONFIG(2'd2, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);
    `SET_STAGE_CONFIG(2'd3, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);

    `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t1, initial");
    `SET_ARMED;

    duv_if.cb.smpls_i <= 'h2;
    repeat (10) begin
      duv_if.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o  == 'b0, "t2, trigger with too low level");
      duv_if.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o  == 'b0, "t2, trigger with too low level 2");
    end

    // increase level, let stage0 match
    duv_if.cb.smpls_i <= 'h1;
    duv_if.cb.stb_i   <= 'b1;
    `CLK_DELAY
    duv_if.cb.smpls_i <= 'h1;
    duv_if.cb.stb_i   <= 'b0;

    repeat (10) begin
      duv_if.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o  == 'b0, "t2, level ok, no trigger");
      duv_if.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.cb.run_o  == 'b0, "t2, level ok, no trigger");
    end

    // match trigger condition
    duv_if.cb.smpls_i <= 'h2;
    duv_if.cb.stb_i   <= 'b1;
    `CLK_DELAY
    `CLK_DELAY
    `CLK_DELAY
    duv_if.cb.stb_i   <= 'b0;
    `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b1, "t2 triggered");

    `SET_RESET;

    ////////////// TEST 3 //////////////
    // One stage, low level, delay
    //
    //               st       mask         value
    `SET_STAGE_VAL(2'd0, 32'h80000000, 32'h7FFFFFFF);
    `SET_STAGE_VAL(2'd1, 32'h00000000, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd2, 32'h00000000, 32'hFFFFFFFF);
    `SET_STAGE_VAL(2'd3, 32'h00000000, 32'hFFFFFFFF);

    //                stg  dly_l dly_h ch[3:0] ch[4] lvl  start  ser
    `SET_STAGE_CONFIG(2'd0, 8'h4, 8'h0, 4'd0, 1'd0, 2'd0, 1'd1, 1'd0);
    `SET_STAGE_CONFIG(2'd1, 8'h0, 8'h0, 4'd0, 1'd0, 2'd1, 1'd0, 1'd0);
    `SET_STAGE_CONFIG(2'd2, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);
    `SET_STAGE_CONFIG(2'd3, 8'h0, 8'h0, 4'd0, 1'd0, 2'd0, 1'd0, 1'd0);

    `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t3, initial");
    `SET_ARMED;

    duv_if.cb.smpls_i <= 'b0;
    duv_if.cb.stb_i   <= 'b1;
    `CLK_DELAY
    duv_if.cb.stb_i   <= 'b0;
    `CLK_DELAY
    `CLK_DELAY
    `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t3 triggered waiting for delay");
    repeat(8) `CLK_DELAY `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b0, "t3 triggered waiting for delay loop");
    duv_if.cb.stb_i   <= 'b1;
    repeat(5) `CLK_DELAY;
    `CLK_DELAY `SCORE_ASSERT_STR(duv_if.cb.run_o == 'b1, "t3 triggered");

    duv_if.cb.stb_i   <= 'b0;
    `SET_RESET;



    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
