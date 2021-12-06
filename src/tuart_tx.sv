/*
 * file: tuart_tx.sv
 * usage: Tiny-UART transmitter implementation.
 *
 * 1 start bit, 1 stop bit, variable data bits
 * 
 */

 `default_nettype none

 module tuart_tx #(parameter CMD_WIDTH,
                   parameter DATA_BITS,
                   parameter SYS_CLK_F,
                   parameter BAUD_RATE) ( // General
                                          input  logic                  clk_i,
                                          input  logic                  rst_in,
                                          input  logic                  smpl_i,
                                          // External communication
                                          input  logic                  rx_i,
                                          // Connection to LogIP core
                                          output logic [CMD_WIDTH-1:0]  data_i,
                                          input  logic                  stb_i);

  // TODO

 endmodule
 
 