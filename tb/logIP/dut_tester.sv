/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

program logIP_tester ( dut_if.tb duv_if, 
                      input clk_i, 
                      input score_mbox_t mbx,
                      input Client i_client);

  import logIP_pkg::*;
  import tb_pkg::*;

  byte rx_byte;


  initial begin
    $display("----- Started ------");

    // Basic tests for client uart
    `SCORE_ASSERT(i_client.i_uart8.is_receive_empty());
    i_client.i_uart8.transmit('h44);
    i_client.i_uart8.wait_transmit_done();
    `SCORE_ASSERT(!i_client.i_uart8.is_receive_empty());
    i_client.i_uart8.receive(rx_byte);
    `SCORE_ASSERT(rx_byte == 'h44);
    `SCORE_ASSERT(i_client.i_uart8.is_receive_empty());
    i_client.query_id();
    i_client.i_uart8.wait_transmit_done();
    `SCORE_ASSERT(!i_client.i_uart8.is_receive_empty());
    i_client.i_uart8.transmit('h44);
    i_client.i_uart8.wait_transmit_done();
    `SCORE_ASSERT(!i_client.i_uart8.is_receive_empty());
    i_client.i_uart8.receive(rx_byte);
    `SCORE_ASSERT(rx_byte == byte'(CMD_S_ID));
    `SCORE_ASSERT(!i_client.i_uart8.is_receive_empty());
    i_client.i_uart8.receive(rx_byte);
    `SCORE_ASSERT(rx_byte == 'h44);
    `SCORE_ASSERT(i_client.i_uart8.is_receive_empty());


    //
    // TODO: Top level tests.
    //


    `SCORE_DONE 
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
