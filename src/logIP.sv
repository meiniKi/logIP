/*
 * file: logIP.sv
 * usage: Top level module for logIP.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module logIP #( parameter WIDTH = 32,
                parameter UART_CLK_PER_BIT = 10) (
  input  logic              clk_i,    //! system clock
  input  logic              rst_in,   //! system reset
  input  logic [WIDTH-1:0]  chls_i,   //! input channels
  input  logic              rx_i,     //! uart receive
  output logic              tx_o      //! uart transmit
);

assign tx_o = rx_i;
// TODO

endmodule