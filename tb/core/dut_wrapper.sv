/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);

  core  dut ( .clk_i          (ifc.clk_i),
              .rst_in         (ifc.rst_in),
              .input_i        (ifc.input_i),
              .cmd_i          (ifc.cmd_i),
              .exec_i         (ifc.exec_i),
              .we_o           (ifc.we_o),
              .addr_o         (ifc.addr_o),
              .mem_i          (ifc.mem_i),
              .mem_o          (ifc.mem_o),
              .tx_rdy_i       (ifc.tx_rdy_i),
              .tx_stb_o       (ifc.tx_stb_o),
              .tx_o           (ifc.tx_o),
              .tx_xon_o       (ifc.tx_xon_o),
              .tx_xoff_o      (ifc.tx_xoff_o));
endmodule