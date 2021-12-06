/*
 * file: indec.sv
 * usage: SUMP instruction decoder
 *
 */

`default_nettype wire
`timescale 1ns/1ps;
module indec (
              // General
              input  logic        clk_i,
              input  logic        rst_in,
              // Input
              input  logic        stb_i,
              input  logic [ 7:0] opc_i,
              input  logic [31:0] cmd_i,
              // Output
              output logic        sft_rst_o,
              output logic        armd_o,
              output logic        id_o,
              output logic        xon_o,
              output logic        xoff_o,
              output logic        set_mask_o,
              output logic        set_val_o,
              output logic        set_cfg_o,
              output logic        set_div_o,
              output logic        set_cnt_o,
              output logic        set_flgs_o,
              output logic [ 1:0] stg_o,
              // TODO: introduce reg if shortens critical path
              output logic        stb_o
              );

  import logIP::*;
  
  logic opcode_t opc;

  assign opc    = opcode_t'(opc_i);
  assign stg_o  = cmd_i[3:2];
  assign stb_o  = stb_i;

  always_comb begin : opcode_decoding
    // Default values
    sft_rst_o   = 'b0;
    armd_o      = 'b0;
    id_o        = 'b0;
    xon_o       = 'b0;
    xoff_o      = 'b0;
    set_mask_o  = 'b0;
    set_cfg_o   = 'b0;
    set_val_o   = 'b0;
    set_div_o   = 'b0;
    set_cnt_o   = 'b0;
    set_flgs_o  = 'b0;

    casex (opc) begin
      CMD_S_SOFT_RESET:         sft_rst_o   = 'b1;
      CMD_S_RUN:                armd_o      = 'b1;
      CMD_S_ID:                 id_o        = 'b1;
      CMD_S_XON:                xon_o       = 'b1;
      CMD_S_XOFF:               xoff_o      = 'b1;
      CMD_L_MSK_SET_TRG_MSK:    set_mask_o  = 'b1;
      CMD_L_MSK_SET_TRG_VAL:    set_val_o   = 'b1;
      CMD_L_MSK_SET_TRG_CONF:   set_cfg_o   = 'b1;
      CMD_L_MSK_SET_DIV:        set_div_o   = 'b1;
      CMD_L_MSK_SET_RD_DLY_CNT: set_cnt_o   = 'b1;
      CMD_L_MSK_SET_FLAGS:      set_flgs_o  = 'b1;
    end
  end


`ifdef FORMAL

  always_comb begin
    assert ($onehot({ sft_rst_o, armd_o, id_o, xon_o, 
                      xoff_o, set_mask_o, set_cfg_o, 
                      set_val_o, set_div_o, set_cnt_o,
                      set_flgs_o }));
  end

`endif


endmodule