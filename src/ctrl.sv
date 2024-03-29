/* Copyright (C) 2021-2022 Meinhard Kissich
 * Copyright (C) 2021-2022 Klaus Weinbauer
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
 * file: ctrl.sv
 * usage: Main FSM
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module ctrl #(
  localparam WIDTH = 32,
  parameter DEPTH=5                         //! memory depth / address width
) (           
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  input  logic                  set_cnt_i,  //! configure the amount of samples to return
  input  logic [WIDTH-1:0]      cmd_i,      //! command data
  input  logic                  run_i,      //! trigger sampling
  input  logic                  stb_i,      //! indicates that sample is ready
  // Memory
  output logic                  we_o,       //! write enable
  output logic [DEPTH-1:0]      addr_o,     //! memory address
  // Transmitter
  input  logic                  tx_rdy_i,   //! transmitter ready flag
  output logic                  tx_stb_o,   //! starts transmitter
  output logic                  tx_sel_o    //! select ram data to write back
);

  localparam CNT_WIDTH = WIDTH / 2;

  typedef enum bit [1:0] { IDLE, TRG, TX, TX_WAIT } states_t;

  states_t state;
  states_t state_next;

  logic [CNT_WIDTH-1:0] rd_cnt;
  logic [CNT_WIDTH-1:0] dly_cnt;

  logic [CNT_WIDTH+3:0] cnt;
  logic [CNT_WIDTH+3:0] cnt_next;

  logic [DEPTH-1:0] ptr;
  logic [DEPTH-1:0] ptr_next;

  assign addr_o   = ptr;
  assign tx_sel_o = (state != IDLE);

  always_comb begin : main_fsm
    // Default
    cnt_next        = cnt;
    state_next      = state;
    we_o            = 'b0;  
    tx_stb_o        = 'b0;
    ptr_next        = ptr;

    case (state)
      // Keep sampling in IDLE to have samples before the trigger
      // available. Once triggered (run_i), transit to TRG.
      //
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

      // Sample another 4*dly_cnt + 4 samples, before transmitting
      // the caputured values to the client.
      //
      TRG: begin
        if (cnt == {dly_cnt, 2'b11}) begin
          state_next      = TX;
          cnt_next        = 'b0;
          ptr_next        = ptr - 1;
        end
        if (stb_i == 'b1) begin
          cnt_next        = cnt + 1;
          we_o            = 'b1;
          ptr_next        = ptr + 1;
        end
      end

      // Read 4*rd_cnt + 4 samples from the ram and transmit
      // those to the client. 
      //
      TX: begin
        if (cnt == {rd_cnt, 2'b11}) begin
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
    end else begin
      state     <= state_next;
      cnt       <= cnt_next;
      ptr       <= ptr_next;
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