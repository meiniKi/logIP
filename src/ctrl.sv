/*
 * file: ctrl.sv
 * usage: Main FSM
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module ctrl #(
  localparam WIDTH = 32,
  parameter DEPTH=5                             //! memory depth / address width
) (           
  // General            
  input  logic                  clk_i,          //! system clock 
  input  logic                  rst_in,         //! system reset, low active
  input  logic                  set_cnt_i,      //! configure the amount of samples to return
  input  logic [WIDTH-1:0]      cmd_i,          //! command data
  input  logic                  run_i,          //! trigger sampling
  input  logic                  stb_i,          //! indicates that sample is ready
  input  logic                  cstb_i,         //! indicates a write from cache into memory
  // Congiuration
  input  logic [3:0]            cfg_i,          //! active channel group
  // Memory
  output logic                  cen_o,          //! write enable
  output logic [DEPTH-1:0]      addr_o,         //! memory address
  // Transmitter
  input  logic                  tx_rdy_i,       //! transmitter ready flag
  output logic                  tx_stb_o,       //! starts transmitter
  output logic                  tx_sel_mem_o,   //! select ram data to write back
  output logic                  tx_sel_cache_o, //! select ram data to write back
  output logic [2:0]            tx_width_o      //! number of bytes to transmit
);

  localparam CNT_WIDTH = WIDTH / 2;

  typedef enum bit [2:0] { IDLE, TRG, TX, TX_CACHE, TX_WAIT } states_t;

  states_t state;
  states_t state_next;

  logic [CNT_WIDTH-1:0] rd_cnt;
  logic [CNT_WIDTH-1:0] dly_cnt;

  logic [CNT_WIDTH+3:0] cnt;
  logic [CNT_WIDTH+3:0] cnt_next;

  logic [DEPTH-1:0] ptr;
  logic [DEPTH-1:0] ptr_next;

  // Count the number of elements
  // currently being stored in the cache
  //
  logic [1:0] c_cnt;
  logic [1:0] c_cnt_next;

  // Number of memmory elements to read back
  // in the TX state
  logic [CNT_WIDTH+3:0] rd_mem_cnt;

  // Number of active channel groups
  //
  logic [2:0] cfg_ones;

  assign addr_o         = ptr;
  assign tx_sel_mem_o   = (state != IDLE);
  assign tx_sel_cache_o = (state == TX_CACHE);

  // The number of stages is low, successive addition seems to
  // be the most efficient way
  //
  assign rd_mem_cnt  =  (cfg_ones == 1) ? (rd_cnt + 'd1)      :
                        (cfg_ones == 2) ? (rd_cnt + 'd1) << 1 :
                        (cfg_ones == 3) ? (rd_cnt + rd_cnt + rd_cnt + 'd3) :
                                          (rd_cnt + 'd1) << 2;

  always_comb begin : active_channel_groups
    cfg_ones    = 'b0;
    foreach(cfg_i[idx]) begin
      cfg_ones    += cfg_i[idx];
    end
  end // always_comb


  always_comb begin : main_fsm
    // Default
    cnt_next        = cnt;
    state_next      = state;
    tx_stb_o        = 'b0;
    ptr_next        = ptr;
    c_cnt_next      = c_cnt;
    cen_o           = 'b0;
    tx_width_o      = WIDTH >> 3;

    case (state)
      // Keep sampling in IDLE to have samples before the trigger
      // available. Once triggered (run_i), transit to TRG.
      //
      IDLE: begin
        cen_o       = 'b1;
        c_cnt_next  = c_cnt + cfg_ones;
        if (run_i == 'b1) begin
          state_next      = TRG;
          cnt_next        = 'b0;
        end
        if (cstb_i == 'b1) begin
          ptr_next        = ptr + 1;
        end        
      end

      // Sample another 4*dly_cnt + 4 samples, before transmitting
      // the caputured values to the client.
      //
      TRG: begin
        cen_o       = 'b1;
        c_cnt_next  = c_cnt + cfg_ones;
        if (cnt == {dly_cnt, 2'b11}) begin
          state_next      = TX;
          cnt_next        = 'b0;
          ptr_next        = ptr - 1;
        end
        if (cstb_i == 'b1) begin
          cnt_next        = cnt + 1;
          ptr_next        = ptr + 1;
        end
      end

      // First, the cached samples are sent back (if not emppty).
      // This is at a maximum one transfers, so TX_WAIT can directly
      // jump to the TX state to read back further samples from memory.
      //
      TX_CACHE: begin
        tx_width_o      = c_cnt;
        state_next      = TX_WAIT;
        tx_stb_o        = 'b1;
      end

      // Read >4*rd_cnt + 4 samples from the ram and transmit
      // those to the client. There might be more samples transmitted
      // to the client. It works but does _not_ conform to the spec.
      //
      TX: begin
        if (cnt == rd_mem_cnt) begin
          state_next      = IDLE;
        end else begin
          state_next      = TX_WAIT;
        end
        cnt_next        = cnt + 1;
        ptr_next        = ptr - 1;
        tx_stb_o        = 'b1;
      end

      // Wait for the transmitter to become ready for
      // transmitting the next sample value.
      //
      TX_WAIT: begin
        if (tx_rdy_i == 'b1) begin
          state_next      = TX;
        end   
      end

      default: state_next = IDLE; 
    endcase
  end // always_comb


  always_ff @(posedge clk_i ) begin : fsm
    if (~rst_in) begin
      state     <= IDLE;
      cnt       <= 'b0;   
      ptr       <= 'b0;
      c_cnt     <= 'b0;
    end else begin
      state     <= state_next;
      cnt       <= cnt_next;
      ptr       <= ptr_next;
      c_cnt     <= c_cnt_next;
    end
  end // always_ff

  always_ff @(posedge clk_i) begin : set_cnt
    if (~rst_in) begin
      rd_cnt    <= 'b0;
      dly_cnt   <= 'b0;
    end else if (set_cnt_i) begin
      rd_cnt    <= cmd_i[15:0];
      dly_cnt   <= cmd_i[31:16];
    end
  end // always_ff

endmodule