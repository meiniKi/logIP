/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);

  logic [31:0]    q_o;
  logic [31:0]    d_i;
  logic           we_o;
  logic [4:0]     addr_o;

  ramif i_ramif ( .clk_i  (ifc.clk_i),
                              .rst_in (ifc.rst_in),
                              .en_i   ('b1),
                              .we_i   (we_o),
                              .addr_i (addr_o),
                              .d_i    (q_o),
                              .q_o    (d_i)
  );

  ctrl #( .CMD_WIDTH (32), 
          .SMPL_WIDTH (32),
          .TX_WIDTH (32)) dut ( .clk_i      (ifc.clk_i),
                                .rst_in     (ifc.rst_in),
                                .set_cnt_i  (ifc.set_cnt_i),
                                .cmd_i      (ifc.cmd_i),
                                .run_i      (ifc.run_i),
                                .stb_i      (ifc.stb_i),
                                .smpls_i    (ifc.smpls_i),
                                .d_i        (d_i),
                                .tx_rdy_i   (ifc.tx_rdy_i),
                                .we_o       (we_o),
                                .addr_o     (addr_o),
                                .q_o        (q_o),
                                .tx_stb_o   (ifc.tx_stb_o),
                                .tx_o       (ifc.tx_o)
    );
endmodule