/*
 * file: cache.sv
 * usage: 
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module cache #(
  parameter INPUT=4,                        //! number of input bytes
  parameter OUTPUT=4                        //! number of output bytes
) (                  
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  input  logic                  cfg_stb_i,  //! configure flag, configuration at cfg_i is valid
  input  logic [INPUT-1:0]      cfg_i,      //! configure active input bytes
  input  logic                  stb_i,      //! indicates that input is ready
  input  logic [(INPUT*8)-1:0]  d_i,        //! input data
  output logic                  stb_o,      //! output is ready
  output logic [(OUTPUT*8)-1:0] q_o         //! output data
);

  typedef enum bit [1:0] { IDLE, TRG, TX, TX_WAIT } states_t;

  states_t state;
  states_t state_next;

  logic [(INPUT+OUTPUT-1)*8-1:0]  cache;
  logic [(INPUT+OUTPUT-1)*8-1:0]  cache_next;
  logic [INPUT-1:0]               cfg;
  logic [$clog2(INPUT+OUTPUT):0]  cnt;
  logic [$clog2(INPUT+OUTPUT):0]  cnt_next;

  always_comb begin : caching
    cache_next      = cache;
    state_next      = state;
    cnt_next        = cnt;
    
    if (cnt_next >= OUTPUT) begin
      cnt_next    = cnt - OUTPUT;
    end
    if (stb_i) begin
      for (integer i = 0; i < INPUT; i=i+1) begin
        if (~cfg[i]) begin
          cnt_next    = cnt_next + 1;
          cache_next  = cache_next << 8;
          for (integer j = 0; j < 8; j++) begin
            cache_next[j]  = d_i[i*8+j];
          end
        end
      end
    end

  end // always_comb

  always_comb begin : assign_output
    q_o   = 'b0;
    stb_o = 'b0;

    if (cnt >= OUTPUT) begin
      stb_o = 'b1;
      
      for (integer i = OUTPUT; i < INPUT+OUTPUT; i=i+1) begin
        if (i - cnt == 'b0) begin
          for (integer j = 0; j < (OUTPUT*8-1); j++) begin
            q_o[j] = cache[(i-OUTPUT)*8+j];
          end
        end
      end
    end
  end // always_comb

  always_ff @(posedge clk_i ) begin : fsm
    if (~rst_in) begin
      state     <= IDLE;
      cache     <= 'b0;
      cnt       <= 'b0;
    end else begin
      state     <= state_next;
      cache     <= cache_next;
      cnt       <= cnt_next;
    end
  end // always_ff

  always_ff @(posedge clk_i) begin : set_cfg
    if (~rst_in) begin
      cfg <= 'b0;     
    end else if (cfg_stb_i) begin
      cfg <= cfg_i;     
    end
  end // always_ff

endmodule