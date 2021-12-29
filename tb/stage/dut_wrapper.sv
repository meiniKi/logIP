/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
stage dut ( .clk_i          (ifc.clk_i),
            .rst_in         (ifc.rst_in),
            .cmd_i          (ifc.cmd_i),     
            .set_mask_i     (ifc.set_mask_i),
            .set_val_i      (ifc.set_val_i), 
            .set_cfg_i      (ifc.set_cfg_i),
            .exec_i         (ifc.exec_i),
            .arm_i          (ifc.arm_i),     
            .stb_i          (ifc.stb_i),     
            .smpls_i        (ifc.smpls_i),  
            .lvl_i          (ifc.lvl_i), 
            .match_o        (ifc.match_o),   
            .run_o          (ifc.run_o));
endmodule