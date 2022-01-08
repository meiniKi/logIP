/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
trigger dut ( .clk_i          (ifc.clk_i),
              .rst_in         (ifc.rst_in),
              .cmd_i          (ifc.cmd_i),     
              .set_mask_i     (ifc.set_mask_i),
              .set_val_i      (ifc.set_val_i), 
              .set_cfg_i      (ifc.set_cfg_i),
              .stg_i          (ifc.stg_i),
              .arm_i          (ifc.arm_i),     
              .stb_i          (ifc.stb_i),     
              .smpls_i        (ifc.smpls_i),
              .run_o          (ifc.run_o));
endmodule