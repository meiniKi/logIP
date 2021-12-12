/*
 * file: indec.sv
 * usage: SUMP instruction decoder
 *
 */

`default_nettype wire
`timescale 1ns/1ps
module indec (
              // General
              input  logic          clk_i,
              input  logic          rst_in,
              // Input
              input  logic          stb_i,
              input  logic [ 7:0]   opc_i,
              input  logic [31:0]   cmd_i,
              // Output
              output logic          sft_rst_o,
              output logic          arm_o,
              output logic          id_o,
              output logic          set_mask_o,
              output logic          set_val_o,
              output logic          set_cfg_o,
              output logic          set_div_o,
              output logic          set_cnt_o,
              output logic          set_flgs_o,
              output logic [ 1:0]   stg_o,
              // TODO: introduce reg if shortens critical path
              output logic          stb_o,
              // Flow Control
              output logic          xstb_o,
              output logic          xon_o,
              output logic          xoff_o,
              // OLS extension
              output logic          rd_meta_o,
              output logic          fin_now_o,
              output logic          rd_inp_o,
              output logic          arm_adv_o,
              output logic          set_adv_cfg_o,
              output logic          set_adv_dat_o);

  import logIP_pkg::*;
  
  opcode_t opc;

  assign opc          = opcode_t'(opc_i);
  assign stg_o        = opc_i[3:2];
  assign stb_o        = stb_i;
  assign xstb_o       = stb_i;

  always_comb begin : opcode_decoding
    // Default values
    sft_rst_o     = 'b0;
    arm_o         = 'b0;
    id_o          = 'b0;
    xon_o         = 'b0;
    xoff_o        = 'b0;
    set_mask_o    = 'b0;
    set_cfg_o     = 'b0;
    set_val_o     = 'b0;
    set_div_o     = 'b0;
    set_cnt_o     = 'b0;
    set_flgs_o    = 'b0;

    rd_meta_o     = 'b0;
    fin_now_o     = 'b0;
    rd_inp_o      = 'b0;
    arm_adv_o     = 'b0;
    set_adv_cfg_o = 'b0;
    set_adv_dat_o = 'b0;

    casex (opc) 
      CMD_S_SOFT_RESET:         sft_rst_o     = 'b1;
      CMD_S_RUN:                arm_o         = 'b1;
      CMD_S_ID:                 id_o          = 'b1;
      CMD_S_XON:                xon_o         = 'b1;
      CMD_S_XOFF:               xoff_o        = 'b1;
      CMD_L_MSK_SET_TRG_MSK:    set_mask_o    = 'b1;
      CMD_L_MSK_SET_TRG_VAL:    set_val_o     = 'b1;
      CMD_L_MSK_SET_TRG_CONF:   set_cfg_o     = 'b1;
      CMD_L_MSK_SET_DIV:        set_div_o     = 'b1;
      CMD_L_MSK_SET_RD_DLY_CNT: set_cnt_o     = 'b1;
      CMD_L_MSK_SET_FLAGS:      set_flgs_o    = 'b1;

      // only consider OLS commands if enabled
      //
`ifdef P_OLS_EXTENSION_ENABLED
      CMD_OLS_QUERY_META_DATA:  rd_meta_o     = 'b1;
      CMD_OLS_FINISH_NOW:       fin_now_o     = 'b1;
      CMD_OLS_QUERY_INPUT_DATA: rd_inp_o      = 'b1;
      CMD_OLS_ARM_ADV_TRG:      arm_adv_o     = 'b1;
      CMD_OLS_ADV_TRG_CONG:     set_adv_cfg_o = 'b1;
      CMD_OLS_ADV_TRG_DATA:     set_adv_dat_o = 'b1;
`endif
    endcase
  end



`ifdef FORMAL

  always_comb begin
    assert ($onehot({ sft_rst_o, armd_o, id_o, set_mask_o, set_cfg_o, 
                      set_val_o, set_div_o, set_cnt_o, set_flgs_o }));
  end

`endif


endmodule