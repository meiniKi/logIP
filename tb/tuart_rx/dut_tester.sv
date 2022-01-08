/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define BUS_BIT_DELAY       #(CLK_PERIOD_HALF*DS)
`define BUS_HALF_BIT_DELAY  #(CLK_PERIOD_HALF*DS/2)

program uart_rx_tester ( dut_if.tb duv_if, input clk_i, input score_mbox_t mbx);
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;

    // ##### Test a short command #####
    // Start bit
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;

    // For short command first bit has to be zero
    repeat(7) `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;

    $write("[INFO] Waiting for posedge on strobe... ");
    `BUS_HALF_BIT_DELAY @(posedge duv_if.cb.stb_o);
    `SCORE_ASSERT_STR(duv_if.cb.opc_o == 'h7F, "t0, cmd");
    $display("DONE");

    // Stop bit
    `BUS_HALF_BIT_DELAY duv_if.cb.rx_i <= 1;


    // ##### Test a long command #####
    repeat (4) begin
      `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    
      repeat(9) `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    end

    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    repeat(8) `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    $write("[INFO] Waiting for posedge on strobe... ");
    `BUS_HALF_BIT_DELAY @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT_STR(duv_if.cb.opc_o == 'hFF, "t1, opc");
    `SCORE_ASSERT_STR(duv_if.cb.cmd_o == 'hFFFFFFFF, "t1, cmd");
    `BUS_HALF_BIT_DELAY duv_if.cb.rx_i <= 1; 

    // ##### Test concurrent short commands #####
    
    // First short command
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;             // Start bit
    repeat(7) `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    $write("[INFO] Waiting for posedge on strobe... ");
    `BUS_HALF_BIT_DELAY @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT_STR(duv_if.cb.opc_o == 'h7F, "t2, opc");
    `BUS_HALF_BIT_DELAY duv_if.cb.rx_i <= 1;        // Stop bit

    // Second short command
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;             // Start bit
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    repeat(7) `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    $write("[INFO] Waiting for posedge on strobe... ");
    `BUS_HALF_BIT_DELAY @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT_STR(duv_if.cb.opc_o == 'h01, "t2, opc2");
    `BUS_HALF_BIT_DELAY duv_if.cb.rx_i <= 1;        // Stop bit

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
