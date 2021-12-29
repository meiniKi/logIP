/*
 * file: tuart_rx.sv
 * usage: Tiny-UART receiver implementation for SUMP protocol
 *
 * 1 start bit, 1 stop bit, variable data bits
 * there is no timeout or error handling
 */

`default_nettype wire
`timescale 1ns/1ps
module tuart_rx #(  parameter WORD_BITS = 8,
                    parameter OPC_WORDS = 1,
                    parameter CMD_WORDS = 4,
                    parameter CLK_PER_SAMPLE = 4) (
  // General
  input  logic                            clk_i,      //! system clock
  input  logic                            rst_in,     //! system reset, low active
  // External communication
  input  logic                            rx_i,       //! uart rx input
  // Connection to LogIP core
  output logic [WORD_BITS*OPC_WORDS-1:0]  opc_o,      //! received opcode
  output logic [WORD_BITS*CMD_WORDS-1:0]  cmd_o,      //! received command
  output logic                            stb_o       //! flag, receive complete
);

  localparam OUT_WIDTH = WORD_BITS*(CMD_WORDS+OPC_WORDS);

  typedef enum bit [1:0] {IDLE, TRIG, SAMPLE, STOP} states_t;

  states_t state;
  states_t state_next;

  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt;
  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt_next;
  logic [$clog2(CLK_PER_SAMPLE+1)-1:0]  smpl_cnt_compare;

  logic [$clog2(WORD_BITS)-1:0]         bit_cnt;
  logic [$clog2(WORD_BITS)-1:0]         bit_cnt_next;

  logic [$clog2(CMD_WORDS+1)-1:0]       word_cnt;
  logic [$clog2(CMD_WORDS+1)-1:0]       word_cnt_next;

  logic [OUT_WIDTH-1:0]                 shft_data;
  logic [OUT_WIDTH-1:0]                 shft_data_next;

  logic take_smpl;
  logic short_cmd_ready;
  logic long_cmd_ready;

  // Take sample exactly at 1/2 of the bit-time
  //
  assign smpl_cnt_compare = (state == TRIG) ? (CLK_PER_SAMPLE >> 1) 
                                            :  CLK_PER_SAMPLE;
  assign take_smpl        = (smpl_cnt == smpl_cnt_compare - 1);

  // A short command is indicated by the MSB being zero once
  // the first byte is received
  //
  assign short_cmd_ready  = (shft_data[OUT_WIDTH-1] == 0 && (word_cnt == 1));

  // A long-command is ready when all bits are shifted into the
  // receive-register
  //
  assign long_cmd_ready   = (word_cnt == (CMD_WORDS+OPC_WORDS));

  // Split received data into command and opcode. In case of a
  // short command, cmd_o may be invalid.
  //
  assign opc_o = short_cmd_ready ?  shft_data[OUT_WIDTH-1 -: (OPC_WORDS*WORD_BITS)] : 
                                    shft_data[0 +: OPC_WORDS*WORD_BITS];

  assign cmd_o = shft_data[OPC_WORDS*WORD_BITS +: CMD_WORDS*WORD_BITS];

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
      // rx_i is high when idle. Thus, a falling
      // edge indicates the start bit of uart.
      //
      IDLE: begin
        if (rx_i == 'b0) begin
          state_next      = TRIG;
          smpl_cnt_next   =  'b0;
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
          shft_data_next  = {rx_i, shft_data[OUT_WIDTH-1:1]};
          if (bit_cnt == (WORD_BITS - 1)) begin
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
        smpl_cnt_next     = smpl_cnt + 'b1;
        if (take_smpl) state_next = IDLE;
        if (short_cmd_ready || long_cmd_ready) begin
          word_cnt_next   = 'b0;
          stb_o           = 'b1;
          shft_data_next  = 'b0;
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
  default clocking @(posedge clk_i); endclocking
	default disable iff (~rst_in);

  logic f_pre_init = 0;
  logic f_init = 0;
  always_ff @(posedge clk_i) begin : f_initial_reset
    if (!f_init) begin
      if (!f_pre_init)  f_pre_init  <= 1;
      else              f_init      <= 1;
    end
  end

  asme_init_rst:  assume property (~f_init |-> ~rst_in);
  asme_rst_rx:    assume property (disable iff (rst_in) rx_i);
  asme_rst_wcnt:  assume property (disable iff (rst_in) word_cnt == 'b0);

  sequence ustart(s, d);
    ##1 (~s)[*d];
  endsequence

  sequence ub(s, d);
    ##1 ($stable(s))[*(d-1)];
  endsequence

  sequence udata(s, d);
    (ub(s, d))[*8];
  endsequence
  
  sequence ustop(s, d);
    ##1 (s)[*d];
  endsequence

  asme_vld_uart: 
  
  assume property (state == IDLE && $fell(rx_i)  |->  ustart(rx_i, CLK_PER_SAMPLE-1) 
                                                      ##0 udata(rx_i, CLK_PER_SAMPLE)
                                                      ##0 ustop(rx_i, CLK_PER_SAMPLE));
                                                          
  asrt_word_cnt:    assert property (word_cnt <= CMD_WORDS);
  asrt_bit_cnt:     assert property (bit_cnt < WORD_BITS);
  asrt_start:       assert property ((state == IDLE) && $fell(rx_i) |=> $changed(state));
  //asrt_rx_duration: assert property (state == IDLE && $fell(rx_i) |=> ##(1) state == IDLE);
  asrt_no_stb:      assert property (~short_cmd_ready && ~long_cmd_ready |-> ~stb_o);
  asrt_stb:         assert property (state == STOP && (short_cmd_ready || long_cmd_ready) |-> stb_o ##1 ~stb_o);

`endif

endmodule