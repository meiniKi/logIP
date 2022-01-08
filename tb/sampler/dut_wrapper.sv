/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
sampler #(.CHLS(32)) dut (  .clk_i          (ifc.clk_i),
                            .rst_in         (ifc.rst_in),
                            .fdiv_i         (ifc.fdiv_i),
                            .set_div_i      (ifc.set_div_i),
                            .data_i         (ifc.data_i),
                            .smpls_o        (ifc.smpls_o),
                            .stb_o          (ifc.stb_o));
endmodule