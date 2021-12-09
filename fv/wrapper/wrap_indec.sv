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
  output logic          armd_o,
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
  output logic          xon_o,
  output logic          xoff_o,
  output logic          fl_stb_o);

  FlowCtr  xctrl_o();

  assign xon_o    = xctrl_o.Slave.xon;
  assign xoff_o   = xctrl_o.Slave.xoff;
  assign fl_stb_o = xctrl_o.Slave.stb;

  indec i_indec (.*);

endmodule
