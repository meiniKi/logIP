/*
 * file: tb_indec.sv
 * usage: Minimal testbench for formal.
 *
 */


module tb_indec;

  logic          clk_i;
  logic          rst_in;

  logic          stb_i;
  logic [ 7:0]   opc_i;
  logic [31:0]   cmd_i;

  logic          sft_rst_o;
  logic          armd_o;
  logic          id_o;
  logic          set_mask_o;
  logic          set_val_o;
  logic          set_cfg_o;
  logic          set_div_o;
  logic          set_cnt_o;
  logic          set_flgs_o;
  logic [ 1:0]   stg_o;
  logic          stb_o;

  FlowCtr        xctrl_o();

  indec i_indec (.*);

endmodule
