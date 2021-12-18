/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps
`define BUS_BIT_DELAY       #(CLK_PERIOD_HALF*DS)

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

    // Stop bit
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;

    $write("[INFO] Waiting for posedge on strobe... ");
    @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT(duv_if.cb.data_o == 'h7F000000_00);


    // ##### Test a long command #####
    repeat (5) begin
      `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    
      repeat(8) `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
      
      `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    end
    
    $write("[INFO] Waiting for posedge on strobe... ");
    @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT(duv_if.cb.data_o == 'hFFFFFFFF_FF);


    // ##### Test concurrent short commands #####
    
    // First short command
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;             // Start bit
    repeat(7) `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;             // Stop bit

    $write("[INFO] Waiting for posedge on strobe... ");
    @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT(duv_if.cb.data_o == 'h7F000000_00);

    // Second short command
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;             // Start bit
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;
    repeat(7) `BUS_BIT_DELAY duv_if.cb.rx_i <= 0;
    `BUS_BIT_DELAY duv_if.cb.rx_i <= 1;             // Stop bit

    $write("[INFO] Waiting for posedge on strobe... ");
    @(posedge duv_if.cb.stb_o);
    $display("DONE");
    `SCORE_ASSERT(duv_if.cb.data_o == 'h01000000_00);

    `SCORE_DONE

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
