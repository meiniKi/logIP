/*
 * file: stage.sv
 * usage: Minimal SUMP trigger state.
 *        Only a basic sub-set of functions are
 *        supported currently.
 *
 * When the number of synthesized channels is smaller than
 * 32, then the upper (32-x) channles will deliver '0' values.
 * Concatenation happens in the top level module.
 * x ... number of synthesized channels.
 *
 * Todo:
 *    - implement flags (todo: here or top-level?)
 *
 *
 *                       -------------------------
 *                      |   t+3             t+0   | (< time received in tuart_rx )
 * cmd_i is given as:   | MSByte | x | x | LSByte | (< byte order )
 *                      |7 ...  0|  ...  |7 ...  0| (< bit  order )
 *                       -------------------------
 *
 *
 */

`default_nettype wire
`timescale 1ns/1ps
module stage (
  // General
  input  logic              clk_i,      //! system clock
  input  logic              rst_in,     //! system reset, low active
  // Command and Flags
  input  logic [31:0]       cmd_i,      //! command
  input  logic              set_mask_i, //! flag, set trigger mask
  input  logic              set_val_i,  //! flag, set trigger value
  input  logic              set_cfg_i,  //! flag, set trigger configuration
  // Flow 
  input  logic              arm_i,      //! flag, arm trigger
  // Data
  input  logic              stb_i,      //! flag, new data samples
  input  logic [31:0]       smpls_i,    //! sampled channels
  input  logic [1:0]        lvl_i,      //! currently active level
  // Output
  output logic              match_o,    //! flag, trigger matched
  output logic              run_o       //! flag, trigger run
  );

  logic [3:0][7:0]  cmd_bytes;

  logic [31:0]      r_val;
  logic [31:0]      r_mask;
  logic [15:0]      r_dly;
  logic [1:0]       r_lvl;
  logic [31:0]      r_chl;
  logic             r_ser;
  logic             r_act;

  logic [31:0]      comp_vec;
  logic [15:0]      dly_cnt;
  logic [15:0]      dly_cnt_next;

  typedef enum bit [1:0] {IDLE, ARMD, MTCHD} states_t;

  states_t state;
  states_t state_next;

  logic [31:0]      smpls_shft;
  logic             trg_match;

  // Vector to compare the trg_vals to
  assign comp_vec = r_ser ? smpls_shft : smpls_i;

  // For convenience to ease the access of flag bits
  assign cmd_bytes = cmd_i;

  // High, when trigger (+mask) is matched
  assign trg_match = ~(|((comp_vec ^ r_val) & r_mask));


  always_comb begin : next_state_logic
    // Default values
    state_next      = state;
    match_o         = 'b0;
    run_o           = 'b0;
    dly_cnt_next    = dly_cnt;
    case(state)
      IDLE:   if (arm_i)      state_next = ARMD;
      ARMD: begin
        if (trg_match) begin
          state_next = MTCHD;
          dly_cnt_next = 'b0; 
        end
      end
      MTCHD:  
        if (stb_i && lvl_i >= r_lvl) begin
          if (dly_cnt == r_dly) begin
            state_next  = IDLE;
            run_o       = r_act;
            match_o     = 'b1;
          end else begin
            dly_cnt_next = dly_cnt + 1;
          end
        end 
      default:  state_next = IDLE;
    endcase
  end // always_comb


  always_ff @(posedge clk_i) begin : matching
    if (~rst_in) begin
      smpls_shft <= 'b0;
    end else if (stb_i) begin
      smpls_shft <= {smpls_shft[30:0], smpls_i[r_chl]};
    end 
  end // always_ff


  always_ff @(posedge clk_i) begin : fsm
    if (~rst_in) begin
      state     <= IDLE;
      dly_cnt   <= 'b0;
    end else begin
      state     <= state_next;
      dly_cnt   <= dly_cnt_next;
    end 
  end // always_ff


  always_ff @(posedge clk_i) begin : update_configurations
    if (~rst_in) begin
      r_val     <= 'b0;
      r_mask    <= 'b0;
      r_ser     <= 'b0;
      r_act     <= 'b0;
      r_chl     <= 'b0;
      r_dly     <= 'b0;
      r_lvl     <= 'b0;
    end else begin
      if (set_mask_i) r_mask  <= cmd_i[31:0];
      if (set_val_i)  r_val   <= cmd_i[31:0];
      if (set_cfg_i)  begin
        {r_ser, r_act}        <= {cmd_bytes[0][2],    cmd_bytes[0][3]};
        r_chl                 <= {cmd_bytes[0][0],    cmd_bytes[1][7:4]};
        r_dly                 <= {cmd_bytes[2][7:0],  cmd_bytes[3][7:0]};
        r_lvl                 <= cmd_bytes[1][1:0];
      end
    end
  end // always_ff


`ifdef FORMAL
  default clocking @(posedge clk_i); endclocking
	default disable iff (~rst_in);

  logic f_pre_init = 0;
  logic f_init = 0;
  always_ff @(posedge clk_i) begin : f_initial_reset
    if (!f_init) begin
      if (!f_pre_init)  f_pre_init  <= 1;
      else              f_init      <= 1;
    end
  end

  asme_init_rst:  assume property (~f_init |-> ~rst_in);

  asme_corr_flags: assume property ($onehot0({set_mask_i, set_val_i, set_cfg_i, arm_i, stb_i}));

  asrt_nch_regs: assert property (~(|{set_mask_i, set_val_i, set_cfg_i, arm_i, stb_i}) |=>
                                  $stable({r_val, r_mask, r_chl, r_act, r_ser}));


  asrt_shft:      assert property ($rose(stb_i) |=> smpls_shft[31:1] == $past(smpls_shft[30:0]));
  asrt_set_mask:  assert property ($rose(set_mask_i) |=> r_mask == $past(cmd_i));

`endif

endmodule : stage