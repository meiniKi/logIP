/*
 * file: wrap_indec.sv
 * usage: Wrapper for indev.sv for formal.
 *
 */


 module top_indec (
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

  //
  // Append formal checks here
  //

  indec i_indec (.*);

endmodule
