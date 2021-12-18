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

    // Reset and query ID
    //
    `SCORE_ASSERT(i_client.i_uart8.is_receive_empty());
    repeat(5) i_client.i_uart8.transmit('h44);
    i_client.i_uart8.wait_transmit_done();

    `SCORE_ASSERT(i_client.i_uart8.is_receive_empty());
    i_client.query_id();
    i_client.i_uart8.wait_transmit_done();
    #500;    

    `SCORE_ASSERT(!i_client.i_uart8.is_receive_empty());
    while (!i_client.i_uart8.is_receive_empty()) begin
      #500;
      i_client.i_uart8.receive(rx_byte);
      $display("test received: %c", rx_byte);
    end


    //
    // TODO: Top level tests.
    //


    `SCORE_DONE 
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
