/*
 * file: rdback.sv
 * usage:
 *
 * Without OLS extensions, the readback only provides the device's ID.
 * When OLS instructions are supported, the client can read back parameters
 * that span over multiple words. As the read-back and the transmission of 
 * samples are disjunct phases, the FSMs are split (ctrl vs. rdback).
 */

`default_nettype wire
`timescale 1ns/1ps

module rdback (
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  input  logic                  exec_i,     //! execute command
  input  logic                  tx_rdy_i,   //! transceiver is ready
  // Select readback data
  input  logic                  id_i,       //! flag to read back id
  input  logic                  rd_meta_i,  //! request OLS meta data
  output logic [31:0]           tx_o,       //! transmit data output
  output logic                  stb_o       //! strobe transmit 
);

  typedef enum bit [3:0] {IDLE, WAIT, SEND} states_t;

  states_t      state;
  states_t      state_next;

  logic [2:0]   cnt;
  logic [2:0]   cnt_next;

  logic         last_data;

  logic [32:0]  data_table [0:5];

  /* TODO: splitting, maybe by packed array? */
  assign data_table =
    { {1, "SLA1"},                    /* SUMP ID          */
      {0, 8'h21, MSB 32'd1024},           /* Sample Memory    */
      {0, 3 LSB,  8'h40, 8'd32, 8'h41, 8'h8}, /* #Probes, Version */
      {0, 8'h22, 24'd100_000_000},    /* Sampling Rate    */
      {0, 8'h1, "Log"},               /* Device Name 0    */
      {1, "IP", 16'h0}                /* Device Name 1    */
    };


  assign tx_o       = data_table[cnt][31:0];
  assign stb_o      = state == SEND;
  assign last_data  = data_table[cnt][32];

  always_comb begin : main_fsm
    // Default
    state_next  = state;
    cnt_next    = cnt;

    case (state)
      // Wait for trigger signal
      //
      IDLE: begin
        if (id_i | rd_meta_i) state_next  = WAIT;
        if (id_i)             cnt_next    = 'd0;
        if (rd_meta_i)        cnt_next    = 'd1;
      end

      // Wait for the transmitter to get ready
      //
      WAIT: begin
        if (tx_rdy_i) state_next = SEND; 
      end
      
      // Send the next data
      //
      SEND: begin
        cnt_next = cnt + 'b1;
        if (last_data)  state_next = IDLE;
        else            state_next = SEND;
      end
    endcase
  end


  always_ff @(posedge clk_i) begin
    if (~rst_in) begin
      state     <= IDLE;
      cnt       <= 'b0;
    end else begin
      state     <= state_next;
      cnt       <= cnt_next;
    end
  end

endmodule