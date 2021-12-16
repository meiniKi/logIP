/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);

  logic [31:0]    d_o;
  logic [31:0]    d_i;
  logic           wrt_o;
  logic           read_o;

  mmu #(  .WIDTH (32),
          .DEPTH (4)) i_mmu ( .clk_i  (ifc.clk_i),
                              .rst_in (ifc.rst_in),
                              .read_i (read_o),
                              .wrt_i  (wrt_o),
                              .d_i    (d_o),
                              .d_o    (d_i)
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
                                .read_o     (read_o),
                                .wrt_o      (wrt_o),
                                .d_o        (d_o),
                                .tx_stb_o   (ifc.tx_stb_o),
                                .tx_o       (ifc.tx_o)
    );
endmodule