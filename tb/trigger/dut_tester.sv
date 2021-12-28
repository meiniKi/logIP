/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`include "trigger_helper.svh"
`default_nettype wire
`timescale 1ns/1ps



program trigger_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  initial begin
    $display("----- Started ------");

    duv_if.tb.cb.smpls_i     <= 'h00000000;
    duv_if.tb.cb.arm_i       <= 'b0;
    duv_if.tb.cb.set_mask_i  <= 'b0;
    duv_if.tb.cb.set_val_i   <= 'b0;
    duv_if.tb.cb.set_cfg_i   <= 'b0;
    duv_if.tb.cb.stb_i       <= 'b0;

    `WAIT_CYCLES(10, clk_i)

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

    `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t0, after-config, no trigger");

    repeat (10)
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t0, after-config, no trigger loop");

    repeat (10) begin
      duv_if.tb.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t0, after-config, strobe, not armed");
      duv_if.tb.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t0, after-config, strobe, not armed 2");
    end

    duv_if.tb.cb.arm_i <= 'b1;
    `CLK_DELAY
    duv_if.tb.cb.arm_i <= 'b0;

    repeat (10) begin
      duv_if.tb.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t0, after-config, strobe, no match");
      duv_if.tb.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t0, after-config, strobe, no match 2");
    end
    
    duv_if.tb.cb.smpls_i <= 'h1; 
    duv_if.tb.cb.stb_i   <= 'b1;
    `CLK_DELAY 
    `CLK_DELAY
    `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b1, "t0 triggered");

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

    `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b0, "t1, initial");
    `SET_ARMED;

    duv_if.tb.cb.smpls_i <= 'h2;
    repeat (10) begin
      duv_if.tb.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o  == 'b0, "t1, trigger with too low level");
      duv_if.tb.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o  == 'b0, "t1, trigger with too low level 2");
    end

    // increase level, let stage0 match
    duv_if.tb.cb.smpls_i <= 'h1;
    duv_if.tb.cb.stb_i <= 'b1;
    `CLK_DELAY
    duv_if.tb.cb.smpls_i <= 'h1;
    duv_if.tb.cb.stb_i <= 'b0;

    repeat (10) begin
      duv_if.tb.cb.stb_i <= 'b1;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o  == 'b0, "t1, level ok, no trigger");
      duv_if.tb.cb.stb_i <= 'b0;
      `CLK_DELAY  `SCORE_ASSERT_STR(duv_if.duv.run_o  == 'b0, "t1, level ok, no trigger");
    end

    // match trigger condition
    duv_if.tb.cb.smpls_i <= 'h1;
    duv_if.tb.cb.stb_i <= 'b1;
    `CLK_DELAY
    `SCORE_ASSERT_STR(duv_if.duv.run_o == 'b1, "t1 triggered");

    `SET_RESET;




    `SCORE_DONE
      
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
