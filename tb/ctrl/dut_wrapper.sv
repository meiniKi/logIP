/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);

  ctrl #( .DEPTH(5)) dut (.clk_i      (ifc.clk_i),
                          .rst_in     (ifc.rst_in),
                          .set_cnt_i  (ifc.set_cnt_i),
                          .cmd_i      (ifc.cmd_i),
                          .run_i      (ifc.run_i),
                          .stb_i      (ifc.stb_i),
                          .we_o       (we_o),
                          .addr_o     (addr_o),
                          .tx_rdy_i   (ifc.tx_rdy_i),
                          .tx_stb_o   (ifc.tx_stb_o),
                          .tx_sel_o   (ifc.tx_sel_o)
  );
endmodule