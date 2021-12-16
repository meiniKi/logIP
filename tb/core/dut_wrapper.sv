/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
core  dut ( .clk_i          (ifc.clk_i),
            .rst_in         (ifc.rst_in),
            .cmd_i          (ifc.cmd_i),
            .input_i        (ifc.input_i),
            .tx_rdy_i       (ifc.tx_rdy_i),
            .mem_i          (ifc.mem_i),
            .we_o           (ifc.we_o),
            .addr_o         (ifc.addr_o),
            .mem_o          (ifc.mem_o),
            .tx_stb_o       (ifc.tx_stb_o),
            .tx_o           (ifc.tx_o));
endmodule