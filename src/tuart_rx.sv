/*
 * file: tuart_rx.sv
 * usage: Tiny-UART receiver implementation.
 *
 * 1 start bit, 1 stop bit, variable data bits
 * 
 */

 `default_nettype wire
 module tuart_rx #(parameter CMD_WIDTH = 32,
                   parameter DATA_BITS = 8,
                   parameter SYS_CLK_F = 100_000_000,
                   parameter BAUD_RATE = 115_200) ( // General
                                                    input  logic                  clk_i,
                                                    input  logic                  rst_in,
                                                    // External communication
                                                    input  logic                  rx_sync_i,
                                                    // Connection to LogIP core
                                                    output logic [CMD_WIDTH-1:0]  data_o,
                                                    output logic                  rdy_o);

  localparam COMPARE_MATCH      = (SYS_CLK_F / BAUD_RATE);
  localparam COMPARE_CNT_BITS   = $clog2(COMPARE_MATCH+1);
  localparam CMD_WORDS          = CMD_WIDTH / DATA_BITS;
  localparam CMD_WORDS_CNT_BITS = $clog2(CMD_WORDS+1);
  localparam DATA_BITS_CNT_BITS = $clog2(DATA_BITS+1);

  typedef enum {IDLE, TRIG, SAMPLE, STOP} states_t;

  states_t state;
  states_t state_next;

  logic [COMPARE_CNT_BITS-1:0]    sample_cnt;
  logic [COMPARE_CNT_BITS-1:0]    sample_cnt_next;

  logic [DATA_BITS_CNT_BITS-1:0]  bit_cnt;
  logic [DATA_BITS_CNT_BITS-1:0]  bit_cnt_next;

  logic [CMD_WORDS_CNT_BITS-1:0]  word_cnt;
  logic [CMD_WORDS_CNT_BITS-1:0]  word_cnt_next;

  logic [CMD_WIDTH-1:0]           shft_data;
  logic [CMD_WIDTH-1:0]           shft_data_next;

  logic                           cmd_done;

  //
  assign data_o   = shft_data;
  assign cmd_done = (word_cnt == CMD_WORDS - 1);
  assign rdy_o    = cmd_done && (state == STOP);
  
  always_comb begin : next_state_logic
    // Default
    state_next          = state;
    sample_cnt_next     = sample_cnt;
    word_cnt_next       = word_cnt;
    bit_cnt_next        = bit_cnt;
    shft_data_next      = shft_data;

    case (state)
      IDLE: begin
        if (rx_sync_i == 'b0) begin
          state_next      = TRIG;
          sample_cnt_next =  'b0;
        end
      end

      TRIG: begin
        sample_cnt_next = sample_cnt + 'b1;
        if (sample_cnt == (COMPARE_MATCH>>1)) begin
          state_next      = SAMPLE;
          sample_cnt_next = 'b0;
        end
      end

      SAMPLE: begin
        sample_cnt_next = sample_cnt + 'b1;
        if (sample_cnt == COMPARE_MATCH) begin
          sample_cnt_next = 'b0;
          bit_cnt_next    = bit_cnt + 'b1;
          shft_data_next  = {rx_sync_i, shft_data[CMD_WIDTH-2:0]};
          if (bit_cnt == DATA_BITS - 'b1) state_next = STOP;
        end
      end

      STOP: begin
        word_cnt_next = cmd_done ? 'b0: word_cnt + 1;
        state_next    = IDLE;
      end

      default: state_next = IDLE; 
    endcase
  end // always_comb
  

  always_ff @(posedge clk_i) begin : shift_reg
    if (!rst_in) begin
      state       <= IDLE;
      sample_cnt  <= 'b0;
      bit_cnt     <= 'b0;
      word_cnt    <= 'b0;
      shft_data   <= 'b0;
    end else begin
      state       <= state_next;
      sample_cnt  <= sample_cnt_next;
      bit_cnt     <= bit_cnt_next;
      word_cnt    <= word_cnt_next;
      shft_data   <= shft_data_next;
    end
  end // always_ff

  //assert property (@(posedge clk_i) disable iff (!rst_in)

  initial begin
    asrt_cmd_multiple_of_word: assert(CMD_WIDTH % DATA_BITS == 0);
  end

 endmodule  
 
 