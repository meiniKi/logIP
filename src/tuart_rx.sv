/*
 * file: tuart_rx.sv
 * usage: Tiny-UART receiver implementation for SUMP protocol
 *
 * 1 start bit, 1 stop bit, variable data bits
 * there is no timeout or error handling
 */

`default_nettype wire
`timescale 1ns/1ps
module tuart_rx #(  parameter DATA_BITS = 8,
                    parameter CMD_WIDTH_WORDS = 5,
                    parameter CLK_PER_SAMPLE = 10) (
        // General
        input  logic                                  clk_i,
        input  logic                                  rst_in,
        // External communication
        input  logic                                  rx_sync_i,
        // Connection to LogIP core
        output logic [DATA_BITS*CMD_WIDTH_WORDS-1:0]  data_o,
        output logic                                  stb_o);

  localparam OUT_WIDTH = DATA_BITS*CMD_WIDTH_WORDS;

  typedef enum bit [1:0] {IDLE, TRIG, SAMPLE, STOP} states_t;

  states_t state;
  states_t state_next;

  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt;
  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt_next;
  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt_compare;

  logic [$clog2(DATA_BITS)-1:0]         bit_cnt;
  logic [$clog2(DATA_BITS)-1:0]         bit_cnt_next;

  logic [$clog2(CMD_WIDTH_WORDS+1)-1:0] word_cnt;
  logic [$clog2(CMD_WIDTH_WORDS+1)-1:0] word_cnt_next;

  logic [OUT_WIDTH-1:0]                 shft_data;
  logic [OUT_WIDTH-1:0]                 shft_data_next;

  logic take_smpl;
  logic short_cmd_ready;
  logic long_cmd_ready;

  // Take sampled exactly at 1/2 of the bit-time
  //
  assign smpl_cnt_compare = (state == TRIG) ? (CLK_PER_SAMPLE >> 1) 
                                            :  CLK_PER_SAMPLE;
  assign take_smpl        = (smpl_cnt == smpl_cnt_compare - 1);

  // The shift register is connected to the output.
  // Todo: reversing the byte-order might be needed.
  //
  assign data_o           = shft_data;

  // A short command is indicated by the MSB being zero once
  // the first byte is received
  //
  assign short_cmd_ready  = (shft_data[OUT_WIDTH-1] == 0 && (word_cnt == 1));

  // A long-command is ready when all bits are shifted into the
  // receive-register
  //
  assign long_cmd_ready = (word_cnt == CMD_WIDTH_WORDS);

  //
  always_comb begin : main_fsm
    // Default
    smpl_cnt_next   = smpl_cnt;
    bit_cnt_next    = bit_cnt;
    word_cnt_next   = word_cnt;
    shft_data_next  = shft_data;
    state_next      = state;
    stb_o           = 'b0;

    case (state)
      // Wait for a transfer to start.
      // rx_sync_i is high when idle. Thus, a falling
      // edge indicates the start bit of uart.
      //
      IDLE: begin
        if (rx_sync_i == 'b0) begin
          state_next      = TRIG;
          smpl_cnt_next   =  'b0;
          shft_data_next  = 'b0;
        end
      end
      
      // Transfer is triggered. Best sampling time is
      // 1/2 bit shifted. This state delays the sampling.
      //
      TRIG: begin
        smpl_cnt_next   = smpl_cnt + 'b1;
        if (take_smpl) begin
          state_next    = SAMPLE;
          smpl_cnt_next = 'b0;
          bit_cnt_next  = 'b0;
        end
      end

      // All bits are sampled at 1/2 bit-time and shifted
      // into the buffer.
      //
      SAMPLE: begin
        smpl_cnt_next     = smpl_cnt + 'b1;
        if (take_smpl) begin
          smpl_cnt_next   = 'b0;
          bit_cnt_next    = bit_cnt + 'b1;
          shft_data_next  = {rx_sync_i, shft_data[OUT_WIDTH-1:1]};
          if (bit_cnt == (DATA_BITS - 1)) begin
            state_next    = STOP;
            word_cnt_next = word_cnt + 1;
          end
        end
      end

      // All bits are sampled. If a command is fully received
      // * 1 bit for short-commands or
      // * 5 bits for long-commands
      // the receiver notifies the system.
      //
      STOP: begin
        smpl_cnt_next   = smpl_cnt + 'b1;
        if (take_smpl) state_next = IDLE;
        if (short_cmd_ready || long_cmd_ready) begin
          word_cnt_next = 'b0;
          stb_o         = 'b1;
        end
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


`ifdef FORMAL
  logic f_init = 0;

  always_ff @(posedge clk_i) begin : f_initial_reset
    if (!f_init) begin
      assume (rst_in == 0);
      f_init = 1;
    end
  end
  
  always_ff @(posedge clk_i) begin
    if (!rst_in) begin
      //
      // Assume valid initial conditions 
      //
      assume (state     == IDLE);
      assume (smpl_cnt  == 'b0);
      assume (bit_cnt   == 'b0);
      assume (word_cnt  == 'b0);
      assume (shft_data == 'b0);
    end else begin
      //
      // Assume state properties due to long
      // receive sequence
      //
      if (state == IDLE) begin
        assume (word_cnt < CMD_WIDTH_WORDS);
        assume (bit_cnt == 'b0);
        assume (rx_sync_i == 1);
      end else if (state == SAMPLE) begin
        assume (word_cnt < CMD_WIDTH_WORDS);
      end
      // TODO
    end

    asrt_word_cnt:          assert (word_cnt <= CMD_WIDTH_WORDS);
    asrt_bit_cnt:           assert (bit_cnt < DATA_BITS);
  end

  //
  // Assume valid uart signal
  //
  logic [$clog2((CLK_PER_SAMPLE*(DATA_BITS+2))+1)-1 : 0] f_bit_cnt;
  logic f_trans_active;
  logic f_old_rx;

  always @(posedge clk_i) begin
    if (!rst_in) begin
      f_bit_cnt       <= 'b0;
      f_trans_active  <= 'b0;
      f_old_rx        <= rx_sync_i;
    end else begin
      if (f_trans_active) begin
        f_bit_cnt         <= f_bit_cnt + 'b1;
        if (f_bit_cnt >= 10*CLK_PER_SAMPLE) begin
          f_bit_cnt       <= 'b0;
          f_trans_active  <= 'b0;
        end
      end else if (!f_trans_active && rx_sync_i && f_old_rx != rx_sync_i) begin
        f_old_rx        <= rx_sync_i;
        f_trans_active  <= 'b1;
      end
    end
  end

  always_comb begin : f_shape_uart_signal
    if (f_bit_cnt >= 0 && f_bit_cnt < CLK_PER_SAMPLE) assume (rx_sync_i == 'b0);
    if (f_bit_cnt >= 9*CLK_PER_SAMPLE && f_bit_cnt < 10*CLK_PER_SAMPLE) assume (rx_sync_i == 'b0);
    if (!f_trans_active) assume (f_bit_cnt == 'b0);
  end 
`endif

endmodule  
 
 