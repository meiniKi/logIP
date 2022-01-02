/*
 * file: top.sv
 * usage: Demo top level
 *
 */

module top (
  input  logic        clk,
  input  logic        btnC,
  // Uart Communication
  input  logic        uart_rx_i,
  output logic        uart_tx_o
);

  localparam CLK_PER_BIT = 100_000_000 / 115_200;

  //logic         sys_clk;
  logic         rst;
  logic         lckd;
  logic [31:0]  chls;

  assign rst = ~btnC; // acive low? todo

  /*
  sys_clk_gen i_sys_clk_gen
  (
    .sys_clk  (sys_clk),
    .reset    (rst),
    .locked   (lckd),
    .clk_in1  (clk)
  );
  */

  tpg #(.CHLS(32)) i_tpg (
    .clk_i    (clk),
    .rst_in   (rst),
    .chls     (chls)
  );


  logIP #(.CHLS(32),
          .MEM_DEPTH(10),
          .UART_CLK_PER_BIT(CLK_PER_BIT)) i_logIP (
    .clk_i    (clk), 
    .rst_in   (rst),
    .chls_i   (chls),
    .rx_i     (uart_rx_i),  
    .tx_o     (uart_tx_o)
  );

endmodule

