/*
 * file: controller.sv
 * usage: Main FSM
 *
 */

`default_nettype wire
`timescale 1ns/1ps;
module ctrl #(
  parameter DEPTH=5                         //! memory depth / address width
) (           
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  
  input  logic                  set_cnt_i,  //! configure the amount of samples to return
  input  logic [WIDTH-1:0]      cmd_i,      //! command data
  input  logic                  run_i,      //! trigger sampling
  input  logic                  stb_i,      //! indicates that sample is ready
  input  logic [WIDTH-1:0]      smpls_i,    //! sample data
  input  logic [WIDTH-1:0]      d_i,        //! data input
  input  logic                  tx_rdy_i,   //! transmitter ready flag
  output logic                  we_o,       //! write enable
  output logic [DEPTH-1:0]      addr_o,     //! memory address
  output logic [WIDTH-1:0]      q_o,        //! memory output
  output logic                  tx_stb_o,   //! starts transmitter
  output logic [WIDTH-1:0]      tx_o        //! data for the transmitter to send
);

  localparam WIDTH = 32;
  localparam CNT_WIDTH = WIDTH / 2;

  typedef enum bit [1:0] { IDLE, TRG, TX, TX_WAIT } states_t;

  states_t state;
  states_t state_next;

  logic [CNT_WIDTH-1:0] rd_cnt;
  logic [CNT_WIDTH-1:0] dly_cnt;

  logic [CNT_WIDTH+2:0] cnt;
  logic [CNT_WIDTH+2:0] cnt_next;
  logic [DEPTH-1:0] ptr;
  logic [DEPTH-1:0] ptr_next;

  assign q_o    = smpls_i;
  assign tx_o   = d_i;

  always_comb begin : main_fsm
    // Default
    cnt_next        = cnt;
    state_next      = state;
    we_o            = 'b0;  
    tx_stb_o        = 'b0;
    addr_o          = ptr;
    ptr_next        = ptr;

    case (state)
      IDLE: begin
        if (run_i == 'b1) begin
          state_next      = TRG;
          cnt_next        = 'b0;
        end
        if (stb_i == 'b1) begin
          we_o            = 'b1;
          ptr_next        = ptr + 1;
        end        
      end

      TRG: begin
        if (cnt == dly_cnt) begin
          state_next      = TX;
          cnt_next        = 'b0;
        end
        if (stb_i == 'b1) begin
          cnt_next        = cnt + 1;
          we_o            = 'b1;
          ptr_next        = ptr + 1;
        end
      end

      TX: begin
        if (cnt == rd_cnt) begin
          state_next      = IDLE;
        end else begin
          state_next      = TX_WAIT;
          cnt_next        = cnt + 1;
          tx_stb_o        = 'b1;
          ptr_next        = ptr - 1;
          addr_o          = ptr - 1;
        end
      end

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
      state <= IDLE;
      cnt   <= 'b0;   
      ptr   <= 'b0;   
    end else begin
      state <= state_next;
      cnt   <= cnt_next;
      ptr   <= ptr_next;
    end
  end // always_ff

  always_ff @(posedge clk_i) begin : set_cnt
    if (~rst_in) begin
      rd_cnt    <= 'b1;
      dly_cnt   <= 'b1;
    end else if (set_cnt_i) begin
      rd_cnt    <= {cmd_i[23:16], cmd_i[31:24]};
      dly_cnt   <= {cmd_i[7:0], cmd_i[15:8]};
    end
  end // always_ff


endmodule