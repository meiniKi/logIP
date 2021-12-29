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

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 5_000_000;

  byte rx_byte;


  initial begin
    $display("----- Started ------");

    // Reset and query ID
    //
    `SCORE_ASSERT(i_client.i_uart8.is_receive_empty());
    repeat(5) i_client.i_uart8.transmit('h00);
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

    // Trigger mask channel 0 and fire.
    //
    `SCORE_ASSERT_STR(i_client.i_uart8.is_receive_empty(), "trg_ch0, rx empty");
    i_client.set_trigger_mask(0, 'h01);
    i_client.set_trigger_value(0, 'h01);
    i_client.set_sampling_rate(SYS_F, SYS_F/3);
    i_client.i_uart8.wait_transmit_done();
    `WAIT_CYCLES(10, clk_i);
    // todo

    //
    // TODO: Top level tests.
    //


    `SCORE_DONE 
    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
