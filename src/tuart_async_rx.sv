/*
 * file: tuart_async_rx.sv
 * usage: Tiny-UART receiver implementation that handles asynchronous signals.
 *
 * 
 */

 `default_nettype wire
 timeunit 1ns;
 module tuart_async_rx #( parameter DATA_BITS = 8,
                          parameter CMD_WIDTH_WORDS = 5,
                          parameter CLK_PER_SAMPLE = 10) (
          // General
          input  logic                                    clk_i,
          input  logic                                    rst_in,
          // External communication
          input  logic                                    rx_async_i,
          // Connection to LogIP core
          output logic [DATA_BITS*CMD_WIDTH_WORDS-1:0]    data_o,
          output logic                                    rdy_o);

  logic rx_sync;

  syncro #( .WIDTH(1),
            .INIT_VAL(1)) syn (.clk_i   (clk_i),
                               .rst_in  (rst_in),
                               .async_i (rx_async_i),
                               .sync_o  (rx_sync));


  tuart_rx #( .DATA_BITS       (DATA_BITS),
              .CMD_WIDTH_WORDS (CMD_WIDTH_WORDS),
              .CLK_PER_SAMPLE  (CLK_PER_SAMPLE)) i_tuart_rx (.clk_i     (clk_i),
                                                             .rst_in    (rst_in),
                                                             .rx_sync_i (rx_sync),
                                                             .data_o    (data_o),
                                                             .rdy_o     (rdy_o));
                              
 endmodule  
 
 