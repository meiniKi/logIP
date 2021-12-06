/*
 * file: tuart_tx.sv
 * usage: Tiny-UART transmitter implementation.
 *
 * 1 start bit, 1 stop bit, variable data bits
 * 
 */

 `default_nettype none

 module tuart_tx #( parameter DATA_BITS = 8,
                    parameter CMD_WIDTH_WORDS = 5,
                    parameter CLK_PER_SAMPLE = 10)) ( 
        // General
        input  logic                                  clk_i,
        input  logic                                  rst_in,
        // handshake
        input  logic                                  stb_i,
        output logic                                  rdy_o,
        // External communication               
        input  logic                                  tx_o,
        // Flow control               
        input  FlowCtr.Slave                          xctrl_i,               
        // Connection to LogIP core
        output logic [DATA_BITS*CMD_WIDTH_WORDS-1:0]  data_i,
        input  logic                                  stb_i);

  import logIP::*;
  
  xcrtl_t r_xctrl;  // XON/XOFF flow control

  // TODO: large shift-reg or couner cheaper?
  localparam SHFT_WIDTH = CMD_WIDTH_WORDS * (DATA_BITS+4);

  logic [SHFT_WIDTH] shft_reg; 
  logic [SHFT_WIDTH] shft_reg_next; 
  
  logic [$clog2(SHFT_WIDTH+1)-1:0] cnt;
  logic [$clog2(SHFT_WIDTH+1)-1:0] cnt_next;

  typedef enum bit [1:0] {IDLE, TX} states_t;

  states_t state;
  states_t state_next;

  always_comb begin : next_state_logic
    shft_reg_next = shft_reg;
    cnt_next      = cnt;
    state_next    = state;

    case (state) begin
      IDLE: begin
        if (stb_i && r_xctrl == XON) begin
          // TODO generator loop, generic
          shft_reg    = {1'b0, data_i[39:32], 3'b010, data_i[31:24], 3'b010, data_i[23:16], 3'b010, data_i[15:8], 3'b010, data_i[7:0], 1'b0};
          cnt_next    = SHFT_WIDTH;
          state_next  = TX;
        end
      end

      TX: begin
        shft_reg_next = shft_reg << 1;
        if (|cnt == 'b0) state_next = TX;
      end
    end
  end

  always_comb begin : output_logic

    case (state) begin
      IDLE: begin

      end

      TX: begin

      end
    end
  end


  always_ff @(posedge clk_i) begin : fsm
    if (!rst_in) begin
      state_next  <= IDLE;
    end else begin
      shft_reg    <= shft_reg_next;
      cnt         <= cnt_next;
      state       <= state_next;
    end
  end


  always_ff @(posedge clk_i) begin : flow_control
    if (!rst_in) begin
      r_xctrl <= XON;
    end else begin
      if (xctrl_i.stb && xctrl_i.xon)       r_xctrl <= XON;
      else if (xctrl_i.stb && xctrl_i.xoff) r_xctrl <= XOFF;
    end
  end




 endmodule
 
 