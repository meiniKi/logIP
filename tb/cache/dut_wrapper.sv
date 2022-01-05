/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);

  cache #(  .INPUT(4),
            .OUTPUT(4)) 
  dut ( .clk_i      (ifc.clk_i),
        .rst_in     (ifc.rst_in),
        .cfg_stb_i  (ifc.cfg_stb_i),
        .cfg_i      (ifc.cfg_i),
        .stb_i      (ifc.stb_i),
        .d_i        (ifc.d_i),
        .stb_o      (ifc.stb_o),
        .q_o        (ifc.q_o)
  );
endmodule