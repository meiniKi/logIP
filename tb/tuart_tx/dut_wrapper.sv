/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);
tuart_tx #( .WORD_BITS (8),
            .CMD_WORDS (4),
            .CLK_PER_SAMPLE (05)) dut ( .clk_i    (ifc.clk_i),
                                        .rst_in   (ifc.rst_in),
                                        .stb_i    (ifc.stb_i),
                                        .rdy_o    (ifc.rdy_o),
                                        .tx_o     (ifc.tx_o),
                                        .xstb_i   (ifc.xstb_i),
                                        .xoff_i   (ifc.xoff_i),
                                        .xon_i    (ifc.xon_i),
                                        .data_i   (ifc.data_i),
                                        .sel_i    (ifc.sel_i));
endmodule