/*
 * file: stage.sv
 * usage: Minimal SUMP trigger state.
 *        Only a basic sub-set of functions are
 *        supported currently.
 *
 * When the number of channels being used _CHLS_ is
 * smaller than 32, the lower x bits will be used.
 *
 * Todo:
 *    - implement serial mode channel selection
 *    - implement levels
 *    - implement delay
 *    - implement flags (todo: here or top-level?)
 *
 *
 *                       -------------------------
 *                      |   t+3             t+0   | (< time received in tuart_rx )
 * cmd_i is given as:   | MSByte | x | x | LSByte | (< byte order )
 *                      |7 ...  0|  ...  |7 ...  0| (< bit  order )
 *                       -------------------------
 *
 * Notes:
 * - When Configuration.channel >= CHLS: 'unpredable' triggering might happen
 *
 */

`default_nettype wire
`timescale 1ns/1ps;
module stage #( parameter CHLS = 32 )(
                                      // General
                                      input  logic              clk_i,
                                      input  logic              rst_in,
                                      // Command and Flags
                                      input  logic [31:0]       cmd_i,
                                      input  logic              set_mask_i,
                                      input  logic              set_val_i,
                                      input  logic              set_cfg_i,
                                      // Flow 
                                      input  logic              arm_i,

                                      // Data
                                      input  logic              stb_i,
                                      input  logic [CHLS-1:0]   smpls_i,
                                      
                                      // Output
                                      output logic              match_o,
                                      output logic              run_o);

  logic [3:0][7:0]  cmd_bytes;

  logic [CHLS-1:0]          r_val;
  logic [CHLS-1:0]          r_mask;
  logic                     r_ser;
  logic [$clogs(CHLS)-1:0]  r_chl;
  logic                     r_act;

  logic [CHLS-1:0]          comp_vec;

  typedef enum bit [1:0] {IDLE, ARMD, MTCHD} states_t;

  states_t state;
  states_t state_next;

  logic [CHLS-1:0]          smpls_shft;
  logic                     trg_match;

  // Vector to compare the trg_vals to
  assign comp_vec = r_ser ? smpls_shft : smpls_i;

  // For convenience to ease the access of flag bits
  assign cmd_bytes = cmd_i;

  // High, when trigger (+mask) is matched
  assign trg_match = ~(|((comp_vec ^ r_val) & r_mask));


  always_comb begin : next_state_logic
    // Default values
    state_next = state;
    case(stage)
      IDLE:   if (arm_i)      state_next = ARMD;
      ARMD:   if (trg_match)  state_next = MTCHD;
      MTCHD:  
        if (stb_i) begin
          state_next = IDLE;
          /* todo: match_o, run_o */
        end 
      default:  state_next = IDLE;
    endcase
  end // always_comb


  always_ff @(posedge clk_i) begin : matching
    if (~rst_in) begin
      smpls_shft <= 'b0;
    end else if (stb_i) begin
      smpls_shft <= {smpls_shft[CHLS-2:0], smpls_i[r_chl];
    end 
  end // always_ff


  always_ff @(posedge clk_i) begin : fsm
    if (~rst_in) begin
      state <= IDLE;
    end else begin
      state <= state_next;
    end 
  end // always_ff


  always_ff @(posedge clk_i) begin : update_configurations
    if (~rst_in) begin
      r_val     <= 'b0;
      r_mask    <= 'b0;
      r_ser     <= 'b0;
      r_act     <= 'b0;
    end else begin
      if (set_mask_i) r_mask  <= cmd_i[CHLS-1:0];
      if (set_val_i)  r_val   <= cmd_i[CHLS-1:0];
      if (set_cfg_i)  begin
        {r_ser, r_act}        <= {cmd_bytes[3][2], cmd_bytes[3][3]};
        r_chl                 <= {cmd_bytes[3][7:4], cmd_bytes[2][7:4]}[$clogs(CHLS)-1:0];
      end
    end
  end // always_ff










  `ifdef FORMAL

  always @(posedge clk_i) begin
    assume ($onehot({/*TODO*/}));
  end

  `endif

endmodule : stage