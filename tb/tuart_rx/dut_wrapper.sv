/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
tuart_async_rx #( .DATA_BITS       (8),
                  .CMD_WIDTH_WORDS (5),
                  .CLK_PER_SAMPLE  (05)) dut (.clk_i       (ifc.clk_i),
                                              .rst_in      (ifc.rst_in),
                                              .rx_async_i  (ifc.rx_async_i),
                                              .data_o      (ifc.data_o),
                                              .rdy_o       (ifc.rdy_o));
endmodule