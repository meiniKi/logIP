/*
 * file: dut_tester.sv
 * 
 */
`include "declarations.svh"
`default_nettype wire
`timescale 1ns/1ps

`define CLK_DELAY `WAIT_CYCLES(1, clk_i)

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

    duv_if.cb.chls_i <= 'h0;

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
    i_client.set_count_samples(8, 4); // 16 samples before, 16 after trigger
    i_client.set_stage_config(0, 'b1);
    i_client.i_uart8.wait_transmit_done();
    i_client.run();
    `WAIT_CYCLES(20, clk_i);

    duv_if.cb.chls_i <= 'hFFFFFFFF;
    
    // Sigrok simple start
    //
    `WAIT_CYCLES(5000, clk_i);
    i_client.set_trigger_mask(0, 'h00);
    i_client.set_trigger_value(0, 'h00);
    i_client.set_stage_config(0, 'b1);
    i_client.set_sampling_rate(SYS_F, SYS_F/4);
    i_client.set_count_samples(3, 1);
    i_client.set_flags('h02);
    i_client.i_uart8.wait_transmit_done();
    i_client.run();
    `WAIT_CYCLES(20, clk_i);

    duv_if.cb.chls_i <= 'hFFFFFFFF;

     // ##### Test cases #####
    TC_Test_Sampling_On_Counter();


    //
    // TODO: Top level tests.
    //


    `SCORE_DONE 
    $display("----- Done ------");
    #100000 $finish;
  end

  task Input_Counter(int start_cnt, int end_cnt, int delay);
    while (start_cnt < end_cnt) begin
      duv_if.cb.chls_i <= start_cnt++;
      repeat (delay) `CLK_DELAY
    end
  endtask;

  task Expect_Data(int exp_value);
    int act_value = 0;
    byte rx_bytes[4];
    for (int i = 0; i < 4; i++) begin
      while (i_client.i_uart8.is_receive_empty()) `CLK_DELAY 
      i_client.i_uart8.receive(rx_bytes[i]);
    end
    act_value = {rx_bytes[3], rx_bytes[2], rx_bytes[1], rx_bytes[0]};
    `ASSERT_EQ_STR(exp_value, act_value, "Wrong data received.")
  endtask;

  task TC_Test_Sampling_On_Counter();
    duv_if.cb.chls_i  <= 'h00000000;
    i_client.reset();
    repeat (50) `CLK_DELAY;
    i_client.i_uart8.clear_mbx();

    // configure client
    i_client.set_trigger_mask(0, 'h00000001);
    i_client.set_trigger_value(0, 'h00000001);
    i_client.set_sampling_rate(SYS_F, SYS_F/4);
    // Read Count is the number of samples to read back from memory:
    // -> I want to read back 8 samples
    // Delay Count is the number of samples to capture after the trigger fired:
    // -> I want to capture all samples after the trigger 
    i_client.set_count_samples(2, 2);
    i_client.set_stage_config(0, 'b1);
    i_client.i_uart8.wait_transmit_done();
    i_client.run();

    fork
      begin // generate input
        repeat (100) `CLK_DELAY 
        Input_Counter(0, 64, 4);
      end
      begin // Wait and read output
        // Logically we would now expect to receive 8 samples, but
        // we get 12, so why not! (Reason: Compatibility with sump 
        // implementation rather then documentation.)
        for (int i = 12; i >= 1; i--) begin
          Expect_Data(i);
        end
      end
    join

  endtask;

endprogram
