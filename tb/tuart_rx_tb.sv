/*
 * file: tuart_rx_tb.sv
 * usage: Testbench for tuart_rx_tb.sv
 * 
 */

`default_nettype wire

//
interface dut_if ( input logic clk_i );
  //
  import tb_pkg::*;
  
  logic         rst_in;
  logic         rx_sync_i;
  logic [31:0]  data_o;
  logic         rdy_o;

  default clocking cb @(posedge clk_i);
    default input #1step output #(CLK_PERIOD_HALF-1);
    output negedge rst_in;
    output rx_sync_i;
    input  data_o, rdy_o;
  endclocking

  modport duv (input  clk_i,
                      rst_in,
                      rx_sync_i,
              output  data_o,
                      rdy_o);

  modport tb (clocking cb);
endinterface


 // 
module dut_wrapper(dut_if.duv ifc);
  tuart_rx dut(
                .clk_i      (ifc.clk_i),
                .rst_in     (ifc.rst_in),
                .rx_sync_i  (ifc.rx_sync_i),
                .data_o     (ifc.data_o),
                .rdy_o      (ifc.rdy_o));
endmodule

//
module tuart_rx_tb;
  timeunit 1ns;
  import tb_pkg::*;

  logic clk_i  = 0;

  initial begin
    // Dump
    $dumpfile("tuart_rx_tb.vcd");
    $dumpvars(duv_wrapper);
  end

  always begin : clock_gen
    #tb_pkg::CLK_PERIOD_HALF clk_i = 1;
    #tb_pkg::CLK_PERIOD_HALF clk_i = 0;
  end

  dut_if duv_if (clk_i);
  dut_wrapper duv_wrapper (duv_if.duv);
  uart_rx_tester duv_tester(duv_if.tb, clk_i);

endmodule


//
program uart_rx_tester ( dut_if.tb duv_if, input clk_i);

  default clocking duv_if.cb;
  
  import tb_pkg::*;

  localparam SYS_F     = 1_000_000; // TODO
  localparam BAUD      = 10_000;    // TODO
  localparam DS        = (SYS_F / BAUD);

  // Test cmd
  logic [31:0]  tst_cmd = 'h23ABCDEF;

  initial begin
    $display("----- Started ------");

        duv_if.cb.rst_in <= 0;
    ##5 duv_if.cb.rst_in <= 1;

    repeat (4) begin
      ##DS duv_if.cb.rx_sync_i <= 'b0;
      repeat (8) begin
        ##DS  duv_if.cb.rx_sync_i <= tst_cmd[0];
              tst_cmd >>= 1;
      end
      ##DS duv_if.cb.rx_sync_i <= 'b0;
    end
    $display("----- Done ------");
  end

endprogram



