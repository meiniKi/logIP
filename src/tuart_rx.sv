/*
 * file: tuart_rx.sv
 * usage: Tiny-UART receiver implementation.
 *
 * 1 start bit, 1 stop bit, variable data bits
 * there is no timeout or error handling
 */

 `default_nettype wire
 timeunit 1ns;
 module tuart_rx #( parameter DATA_BITS = 8,
                    parameter CMD_WIDTH_WORDS = 5,
                    parameter CLK_PER_SAMPLE = 10) (
        // General
        input  logic                                  clk_i,
        input  logic                                  rst_in,
        // External communication
        input  logic                                  rx_sync_i,
        // Connection to LogIP core
        output logic [DATA_BITS*CMD_WIDTH_WORDS-1:0]  data_o,
        output logic                                  rdy_o);

  localparam OUT_WIDTH = DATA_BITS*CMD_WIDTH_WORDS;

  typedef enum bit [2:0] {IDLE, TRIG, SAMPLE, RDY, STOP, STOP2} states_t;

  states_t state;
  states_t state_next;

  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt;
  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt_next;
  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt_compare;

  logic [$clog2(DATA_BITS)-1:0]         bit_cnt;
  logic [$clog2(DATA_BITS)-1:0]         bit_cnt_next;

  logic [$clog2(CMD_WIDTH_WORDS)-1:0]   word_cnt;
  logic [$clog2(CMD_WIDTH_WORDS)-1:0]   word_cnt_next;

  logic [OUT_WIDTH-1:0]                 shft_data;
  logic [OUT_WIDTH-1:0]                 shft_data_next;

  logic take_smpl;

  assign smpl_cnt_compare = (state == TRIG) ? (CLK_PER_SAMPLE >> 1) 
                                            :  CLK_PER_SAMPLE;
  assign take_smpl        = (smpl_cnt == smpl_cnt_compare - 1);
  assign data_o           = shft_data;

  //
  always_comb begin : main_fsm
    // Default
    smpl_cnt_next   = smpl_cnt;
    bit_cnt_next    = bit_cnt;
    word_cnt_next   = word_cnt;
    shft_data_next  = shft_data;
    rdy_o           = 'b0;

    case (state)
      IDLE: begin
        if (rx_sync_i == 'b0) begin
          state_next    = TRIG;
          smpl_cnt_next =  'b0;
        end
      end
      
      TRIG: begin
        smpl_cnt_next   = smpl_cnt + 'b1;
        if (take_smpl) begin
          state_next    = SAMPLE;
          smpl_cnt_next = 'b0;
          bit_cnt_next  = 'b0;
        end
      end

      SAMPLE: begin
        smpl_cnt_next   = smpl_cnt + 'b1;
        if (take_smpl) begin
          smpl_cnt_next  = 'b0;
          bit_cnt_next   = bit_cnt + 'b1;
          shft_data_next = {rx_sync_i, shft_data[OUT_WIDTH-1:1]};
          if (bit_cnt == (DATA_BITS - 1)) state_next = RDY;
        end
      end

      RDY: begin
        state_next      = STOP;
        smpl_cnt_next   = smpl_cnt + 'b1;
        if (word_cnt == (CMD_WIDTH_WORDS - 1)) begin
          word_cnt_next = 'b0;
          rdy_o         = 'b1;
        end else
          word_cnt_next = word_cnt + 1;
      end

      STOP: begin
        smpl_cnt_next = smpl_cnt + 'b1;
        if (take_smpl) state_next = STOP2;
      end

      STOP2: begin
        if (rx_sync_i) state_next = IDLE;
      end

      default: state_next = IDLE; 
    endcase
  end // always_comb
  

  always_ff @(posedge clk_i) begin : shift_reg
    if (!rst_in) begin
      state     <= IDLE;
      smpl_cnt  <= 'b0;
      bit_cnt   <= 'b0;
      word_cnt  <= 'b0;
      shft_data <= 'b0;

    end else begin
      state     <= state_next;
      smpl_cnt  <= smpl_cnt_next;
      bit_cnt   <= bit_cnt_next;
      word_cnt  <= word_cnt_next;
      shft_data <= shft_data_next;
    end
  end // always_ff

 endmodule  
 
 