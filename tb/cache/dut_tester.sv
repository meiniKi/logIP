/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define CLK_DELAY `WAIT_CYCLES(1, clk_i)

program cache_tester (dut_if duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  task d_in_counter(int start_cnt, int end_cnt, int delay);
    while (start_cnt < end_cnt) begin
      logic [31:0] data = 'b0;
      repeat (4) begin
        data = (data << 8) + start_cnt++;
      end
      `CLK_DELAY  duv_if.cb.d_i <= data;
                  duv_if.cb.stb_i <= 'b1;
      if (delay > 0) begin
        `CLK_DELAY  duv_if.cb.stb_i <= 'b0;
      end
      repeat (delay - 1) `CLK_DELAY 
    end
    `CLK_DELAY  duv_if.cb.stb_i <= 'b0;
  endtask;

  task d_out_validate_counter(int start_cnt, int end_cnt, int concurrent = 0);
    if (concurrent) begin
      @(posedge duv_if.cb.stb_o);
    end
    while (start_cnt < end_cnt) begin
      logic [31:0] exp_data = 'b0;
      repeat (4) begin
        exp_data = (exp_data << 8) + start_cnt++;
      end      
      if (!concurrent) @(posedge duv_if.cb.stb_o);
      `ASSERT_EQ(exp_data, duv_if.cb.q_o);
      if (concurrent) `CLK_DELAY
    end
  endtask;

  task no_output_validate(int length);
    int flag = 0;
    repeat (length) begin
      `CLK_DELAY flag |= duv_if.cb.stb_o;
    end
    `ASSERT_EQ_STR(0, flag, "No more output data expected.");
  endtask;

  task cfg_cache(logic[3:0] disabled_chnls);
    `CLK_DELAY  duv_if.cb.cfg_i <= disabled_chnls;
                duv_if.cb.cfg_stb_i <= 'b1;
    `CLK_DELAY  duv_if.cb.cfg_i <= 'b0;
                duv_if.cb.cfg_stb_i <= 'b0;
  endtask;

  initial begin
    $timeformat(-9, 2, " ns", 12);
    $display("----- Started ------");
    #(100)

    TC_simple_data_passthrough();
    TC_I3O4_First_Disabled();
    TC_I2O4_First_And_Last_Disabled();
    TC_Bytes_Lost_In_Cache();
    TC_Fast_Passthrough();
    TC_I2O4_Fast_Input();

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end  

  task TC_simple_data_passthrough();
    cfg_cache('b0);
    fork
      d_in_counter(0, 8, 4);
      begin
        d_out_validate_counter(0, 8);
        no_output_validate(5);
      end
    join
  endtask

  task TC_I3O4_First_Disabled();
    cfg_cache('b1000);
    fork
      d_in_counter(0, 16, 3);
      begin
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h01020305, duv_if.cb.q_o);
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h0607090A, duv_if.cb.q_o);
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h0B0D0E0F, duv_if.cb.q_o);
        no_output_validate(8);
      end
    join
  endtask

  task TC_I2O4_First_And_Last_Disabled();
    cfg_cache('b1001);
    fork
      d_in_counter(0, 16, 3);
      begin
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h01020506, duv_if.cb.q_o);
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h090A0D0E, duv_if.cb.q_o);
        no_output_validate(8);
      end
    join
  endtask

  task TC_Bytes_Lost_In_Cache();
    cfg_cache('b0111);
    fork
      d_in_counter(0, 12, 3);
      no_output_validate(16);
    join
    `CLK_DELAY duv_if.cb.rst_in <= 'b0;
    `CLK_DELAY duv_if.cb.rst_in <= 'b1;
  endtask

  task TC_Fast_Passthrough();
    cfg_cache('b0);
    fork
      d_in_counter(0, 64, 0);
      begin
        d_out_validate_counter(0, 64, 1);
        no_output_validate(4); 
      end
    join
  endtask

  task TC_I2O4_Fast_Input();
    cfg_cache('b0110);
    fork
      d_in_counter(0, 16, 0);
      begin
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h00030407, duv_if.cb.q_o);
        @(posedge duv_if.cb.stb_o);
        `ASSERT_EQ('h080B0C0F, duv_if.cb.q_o);
        no_output_validate(4);
      end
    join
  endtask

endprogram