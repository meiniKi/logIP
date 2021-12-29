/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
tuart_rx #( .WORD_BITS       (8),
            .CMD_WORDS       (4),
            .OPC_WORDS       (1),
            .CLK_PER_SAMPLE  (05)) dut (.clk_i    (ifc.clk_i),
                                        .rst_in   (ifc.rst_in),
                                        .rx_i     (ifc.rx_i),
                                        .cmd_o    (ifc.cmd_o),
                                        .opc_o    (ifc.opc_o),
                                        .stb_o    (ifc.stb_o));
endmodule