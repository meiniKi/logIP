/*
 * file: tuart_rx.sv
 * usage: Tiny-UART receiver implementation.
 */

 `default_nettype none

 module tuart #(parameter CMD_WIDTH,
                parameter DATA_BITS,
                parameter NR_START_BITS,
                parameter NR_STOP_BITS,
                ) (// General
                                  input  logic              clk_i,
                                  input  logic              rst_in,
                                  input  logic              smpl_i,
                                  // External communication
                                  input  logic              rx_i,
                                  // Connection to LogIP core
                                  output logic [WIDTH-1:0]  data_o,
                                  output logic              rdy_o);

  

  always_ff @(posedge clk) begin : shift_reg
    if (!rst_in) begin
      data_o <= 'b0;
    end else begin
      data_o <= 
    end
  end

 endmodule
 
 