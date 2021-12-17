/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);

  logic [31:0]    q_o;
  logic [31:0]    d_i;
  logic           we_o;
  logic [4:0]     addr_o;

  ramif i_ramif ( .clk_i  (ifc.clk_i),
                              .rst_in (ifc.rst_in),
                              .en_i   ('b1),
                              .we_i   (we_o),
                              .addr_i (addr_o),
                              .d_i    (d_i),
                              .q_o    (q_o)
  );

  core  dut ( .clk_i          (ifc.clk_i),
            .rst_in         (ifc.rst_in),
            .cmd_i          (ifc.cmd_i),
            .input_i        (ifc.input_i),
            .tx_rdy_i       (ifc.tx_rdy_i),
            .mem_i          (q_o),
            .exec_i         (ifc.exec_i),
            .we_o           (we_o),
            .addr_o         (addr_o),
            .mem_o          (d_i),
            .tx_stb_o       (ifc.tx_stb_o),
            .tx_o           (ifc.tx_o));
endmodule