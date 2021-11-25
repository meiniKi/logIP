/*
 * file: tuart.sv
 * usage: Tiny-UART implementation for LogIP core.
 */

`default_nettype none

module tuart 
  #(parameter BAUDRATE) ( // General
                          input  logic        clk_i,
                          input  logic        rst_in,
                          // External communication
                          input  logic        rx_i,
                          output logic        tx_o,
                          // Connection to LogIP core
                          output logic [39:0] cmd_o,
                          output logic        ex_o,
                          input  logic [31:0] data_i,
                          input  logic        stb_i);



endmodule

