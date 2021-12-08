/*
 * file: tuart_tx.sv
 * usage: Tiny-UART transmitter implementation.
 *
 * 1 start bit, 1 stop bit, variable data bits
 * 
 */

`default_nettype wire
module tuart_tx #(  parameter WORD_BITS = 8,
                    parameter CMD_WORDS = 4,
                    parameter CLK_PER_SAMPLE = 10) ( 
      // General
      input  logic                                  clk_i,
      input  logic                                  rst_in,
      // handshake
      input  logic                                  stb_i,
      output logic                                  rdy_o,
      // External communication               
      output logic                                  tx_o,
      // Flow control               
      FlowCtr.Slave                                 xctrl_i,
      // Data               
      input  logic [(WORD_BITS)*(CMD_WORDS)-1:0]    data_i);

  import logIP_pkg::*;

  localparam START_BIT_NR   = 'd12;
  localparam TIME_CNT_START = CLK_PER_SAMPLE - 'b1;

  typedef enum bit [1:0] {IDLE, TX_START, TX_DATA, TX_STOP} states_t;

  logic [WORD_BITS-1:0] shft_reg; 
  logic [WORD_BITS-1:0] shft_reg_next; 
  
  logic [$clog2(WORD_BITS)-1:0] bit_cnt;
  logic [$clog2(WORD_BITS)-1:0] bit_cnt_next;

  logic [$clog2(CMD_WORDS)-1:0] word_cnt;
  logic [$clog2(CMD_WORDS)-1:0] word_cnt_next;

  logic [$clog2(CLK_PER_SAMPLE)-1:0] time_cnt;
  logic [$clog2(CLK_PER_SAMPLE)-1:0] time_cnt_next;

  states_t state;
  states_t state_next;

  xcrtl_t r_xctrl;  // XON/XOFF flow control

  assign rdy_o = (state == IDLE);
  assign tx_o  =  (state == TX_START) ? 'b0 :
                  (state == TX_STOP)  ? 'b1 :
                  (state == TX_DATA)  ? shft_reg[0] :
                                        'b1;

  always_comb begin : next_state_logic
    shft_reg_next = shft_reg;
    bit_cnt_next  = bit_cnt;
    time_cnt_next = time_cnt;
    word_cnt_next = word_cnt;

    case (state)
      // Wait for strobe to start a transfer. XOFF will
      // prevent a new (full) transmission. Pause between
      // a command is not supported.
      //
      IDLE: begin
        if (stb_i && r_xctrl == XON) begin
          state_next    = TX_START;
          bit_cnt_next  = START_BIT_NR;
          word_cnt_next = CMD_WORDS - 'b1;
          time_cnt_next = TIME_CNT_START;
        end
      end

      // Send start bit.
      //
      TX_START: begin
        time_cnt_next   = time_cnt - 'b1;
        if (time_cnt == 'b0) begin
          time_cnt_next = TIME_CNT_START;
          state_next    = TX_DATA;
          shft_reg_next = data_i[word_cnt_next];
          bit_cnt_next  = WORD_BITS - 'b1;
        end
      end

      // Clock out data bits.
      //
      TX_DATA: begin
        time_cnt_next   = time_cnt - 'b1;
        if (time_cnt == 'b0) begin
          time_cnt_next = CLK_PER_SAMPLE;
          bit_cnt_next  = bit_cnt - 'b1;
          shft_reg_next = shft_reg >> 1;
          if (bit_cnt == 'b0) state_next = TX_STOP;
        end
      end

      // Send stop bit.
      //
      TX_STOP: begin
        time_cnt_next   = time_cnt - 'b1;
        if (time_cnt == 'b0) begin
          time_cnt_next = TIME_CNT_START;
          word_cnt_next = word_cnt - 'b1;
          if (word_cnt == 'b0)  state_next = IDLE;
          else                  state_next = TX_START;
        end
      end

      default: state_next = IDLE;
    endcase
  end // always_comb


  always_ff @(posedge clk_i) begin : fsm
    if (!rst_in) begin
      state_next  <= IDLE;
    end else begin
      state    <= state_next;
      shft_reg <= shft_reg_next;
      bit_cnt  <= bit_cnt_next;
      time_cnt <= time_cnt_next;
      word_cnt <= word_cnt_next;
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

endmodule // tuart_tx
 
 