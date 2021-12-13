/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
indec dut ( .clk_i          (ifc.clk_i),
            .rst_in         (ifc.rst_in),
            .stb_i          (ifc.stb_i),
            .opc_i          (ifc.opc_i),
            .sft_rst_o      (ifc.sft_rst_o),
            .arm_o          (ifc.arm_o),
            .id_o           (ifc.id_o),
            .set_mask_o     (ifc.set_mask_o),
            .set_val_o      (ifc.set_val_o),
            .set_cfg_o      (ifc.set_cfg_o),
            .set_div_o      (ifc.set_div_o),
            .set_cnt_o      (ifc.set_cnt_o),
            .set_flgs_o     (ifc.set_flgs_o),
            .stg_o          (ifc.stg_o),
            .stb_o          (ifc.stb_o),
            .xon_o          (ifc.xon_o),
            .xoff_o         (ifc.xoff_o),
            .rd_meta_o      (ifc.rd_meta_o),
            .fin_now_o      (ifc.fin_now_o),
            .rd_inp_o       (ifc.rd_inp_o),
            .arm_adv_o      (ifc.arm_adv_o),
            .set_adv_cfg_o  (ifc.set_adv_cfg_o),
            .set_adv_dat_o  (ifc.set_adv_dat_o));
endmodule