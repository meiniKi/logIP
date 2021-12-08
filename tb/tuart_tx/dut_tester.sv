/*
 * file: dut_tester.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps
program uart_tx_tester (dut_if duv_if, input clk_i );
  import tb_pkg::*;

  localparam SYS_F      = 10_000_000;
  localparam BAUD_RATE  = 2_000_000;

  localparam DS         = 2*(SYS_F / BAUD_RATE);

  logic [4:0][7:0] data = 'h11112222_33334444_55556666_77778888;

  initial begin
    $display("----- Started ------");
    $display("-- %d cycles per bit", DS);

    duv_if.stb_i        = 'b0;
    duv_if.data_i       = 'b0;
    duv_if.xctrl_i.xoff = 'b0;
    duv_if.xctrl_i.xon  = 'b0;
    duv_if.xctrl_i.stb  = 'b0;

    #(10*CLK_PERIOD_HALF*DS)
    duv_if.data_i = data;
    duv_if.stb_i = 'b1;
    #(CLK_PERIOD_HALF*DS) duv_if.stb_i = 'b0;

    $display("----- Done ------");
    #100000 $finish;
  end

endprogram
