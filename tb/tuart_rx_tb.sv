/*
 * file: tuart_rx_tb.sv
 * usage: Testbench for tuart_rx_tb.sv
 * 
 */

`default_nettype none
module tuart_rx_tb;
  timeunit 1ns;

  import tb_pkg::*;

  localparam SYS_F     = 1_000_000; // TODO
  localparam BAUD      = 10_000; // TODO

  localparam DS        = (SYS_F / BAUD);
 
  // DUT inputs
  logic         clk_i     = 0;
  logic         rst_in    = 1;
  logic         rx_sync_i = 0;

  // DUT ouputs
  logic [7:0]   data_o;
  logic         rdy_o;

  // Test cmd
  logic [31:0]  tst_cmd = 'h23ABCDEF;

  always begin : clock_gen
    #tb_pkg::CLK_PERIOD_HALF clk_i = 1;
    #tb_pkg::CLK_PERIOD_HALF clk_i = 0;
  end

  program test_tuart_rx;
    clocking cb_tuart_rx @(posedge clk_i);
      default input #1step output #(CLK_PERIOD_HALF-1);
      output negedge rst_in;
      output rx_sync_i;
      input  data_o, rdy_o;
    endclocking

    initial begin
      $display("----- Started ------");
      // Dump
      $dumpfile("tuart_rx_tb.vcd");
      $dumvars(tuart_rx_i);

          cb_tuart_rx.rst_in <= 0;
      ##5 cb_tuart_rx.rst_in <= 1;

      repeat (4) begin
        ##DS cb_tuart_rx.rx_sync_i <= 'b0;
        repeat (8) begin
          ##DS  cb_tuart_rx.rx_sync_i <= tst_cmd[0];
                tst_cmd >>= 1;
        end
        ##DS cb_tuart_rx.rx_sync_i <= 'b0;
      end
      $display("----- Done ------");
    end

  endprogram

  // Instance
  tuart_rx  #(.CMD_WIDTH( 32    ),
              .DATA_BITS( 8     ),
              .SYS_CLK_F( SYS_F ),
              .BAUD_RATE( BAUD  )) tuart_rx_i (.*);

  // program
  test_tuart_rx T();

endmodule