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
`define TEST_START(name) $display("[INFO] %t | Start test case: '%s'", $time, name);
`define TEST_END(name)   $display("[INFO] %t | End test case: '%s'", $time, name);

program core_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  logic [31:0] counter      = 'b0;

  // TODO

  /*
  task setStageMask(
    input [1:0] stage, 
    input [31:0] mask
  );
     duv_if.cb.cmd_i   <= {4'b1100, stage, 2'b00, mask};   
                duv_if.cb.exec_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.exec_i  <= 'b0;
  endtask

  task setStageValue(
    input [1:0] stage, 
    input [31:0] value
  );
    `CLK_DELAY  duv_if.cb.cmd_i   <= {4'b1100, stage, 2'b01, value};   
                duv_if.cb.exec_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.exec_i  <= 'b0;
  endtask

  task setStageConfig(
    input [1:0]   stage, 
    input [15:0]  delay,
    input [1:0]   level,
    input [4:0]   channel,
    input         serial,
    input         start
  );
    `CLK_DELAY  duv_if.cb.cmd_i   <= {4'b1100, stage, 2'b10, delay, 
                                      channel[3:0], 2'b00, level, 4'b0000, 
                                      start, serial, 1'b0, channel[4]};  
                duv_if.cb.exec_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.exec_i  <= 'b0; 
  endtask

  task cfgStageDefault(
    input [1:0]   stage,
    input [31:0]  mask,
    input [31:0]  value
  );
    setStageMask(stage, mask);
    setStageValue(stage, value);
    setStageConfig(stage, 'b0, 'b0, 'b0, 'b0, 'b1);
  endtask

  task run();
    `CLK_DELAY  duv_if.cb.cmd_i   <= {2'h01, 32'b0};  
                duv_if.cb.exec_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.exec_i  <= 'b0; 
  endtask

  task setReadDelayCnt(
    input [15:0]   read,
    input [15:0]   dly
  );
    `CLK_DELAY  duv_if.cb.cmd_i   <= {8'h81, read[7:0], read[15:8], dly[7:0], dly[15:8]};  
                duv_if.cb.exec_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.exec_i  <= 'b0; 
  endtask

  task setDivider(
    input [23:0] fdiv
  );
    `CLK_DELAY  duv_if.cb.cmd_i   <= {8'h80, fdiv[7:0], fdiv[15:8], fdiv[23:16], 8'b0};  
                duv_if.cb.exec_i  <= 'b1;
    `CLK_DELAY  duv_if.cb.exec_i  <= 'b0; 
  endtask

  task expectRecv(
    input [31:0]  data
  );
    @(posedge duv_if.cb.tx_stb_o);
    if (duv_if.cb.tx_o != data) begin
      $display("[ERROR] @%tns | Expected to receive %h but got %h.", $time, data, duv_if.cb.tx_o );
    end
    `SCORE_ASSERT(duv_if.cb.tx_o == data);
  endtask

  initial begin
    // Upcounting input signal
    forever begin
      #(50) duv_if.cb.input_i <= counter;
      counter <= counter + 1;
    end
  end
  */ 
  initial begin
    $timeformat(-9, 2, " ns", 12);
    $display("##### Start #####");    

    duv_if.cb.tx_rdy_i    <= 'b1;
    duv_if.cb.cmd_i       <= 'b0;
    duv_if.cb.input_i     <= 'b0;
    duv_if.cb.exec_i      <= 'b0;

    `WAIT_CYCLES(10, clk_i);
 
    //testCase1();

    `SCORE_DONE
      
    $display("###### End ######");
    #100000 $finish;
  end


  /*  This test case configures the first stage to trigger at value 8 
  *   in serial mode and read back 4 values, 2 after the trigger and 2 
  *   befor the trigger. 
  */
  /*
  task testCase1();
    `TEST_START("Test Case 1");
    counter <= 'b0;
    cfgStageDefault('b00, 'hFFFFFFFF, 'h00000008);
    setReadDelayCnt('h0004, 'h0002);
    setDivider('h4);
    run();
    expectRecv('h0000000A);
    expectRecv('h00000009);
    expectRecv('h00000008);
    expectRecv('h00000007);
    `TEST_END("Test Case 1");
  endtask
  */

endprogram
