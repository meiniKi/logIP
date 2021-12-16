/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);
ctrl #( .CMD_WIDTH (32), 
        .SMPL_WIDTH (32),
        .TX_WIDTH (32)) dut ( .clk_i      (ifc.clk_i),
                              .rst_in     (ifc.rst_in),
                              .set_cnt_i  (ifc.set_cnt_i),
                              .cmd_i      (ifc.cmd_i),
                              .run_i      (ifc.run_i),
                              .stb_i      (ifc.stb_i),
                              .smpls_i    (ifc.smpls_i),
                              .d_i        (ifc.d_i),
                              .tx_rdy_i   (ifc.tx_rdy_i),
                              .read_o     (ifc.read_o),
                              .wrt_o      (ifc.wrt_o),
                              .d_o        (ifc.d_o),
                              .tx_stb_o   (ifc.tx_stb_o),
                              .tx_o       (ifc.tx_o));
endmodule