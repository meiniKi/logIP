/*
 * file: controller.sv
 * usage: Main FSM
 *
 */

`default_nettype wire
`timescale 1ns/1ps;
module ctrl (
              // General
              input  logic    clk_i,
              input  logic    rst_in,
                
              );

  typedef enum bit [1:0] {IDLE, RX, RX_WAIT} states_t;

  states_t state;
  states_t state_next;

  


  always_ff @( clock ) begin : fsm
    if (~rst_in) begin
      state <= IDLE;
    end else begin
      state <= state_next;
    end
    
  end




endmodule