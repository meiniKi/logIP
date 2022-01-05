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

  logic [(2*INPUT-1)*8-1:0] cache;
  logic [(2*INPUT-1)*8-1:0] cache_next;
  logic [INPUT-1:0]         cfg;
  logic [$clog2(INPUT)-1:0] cnt;
  logic [$clog2(INPUT)-1:0] cnt_next;

  always_comb begin : caching
    cache_next      = cache;
    state_next      = state;
    cnt_next        = cnt;

    if (stb_i) begin
      if (cnt_next >= OUTPUT) begin
        cnt_next    = cnt - OUTPUT;
      end
      generate
        for (i = 0; i < INPUT; i++) begin
          if (~cfg[i]) begin
            cache_next  = cache_next << 8 & d_i[(i+1)*8:i*8];
            cnt_next    = cnt_next + 1;
          end
        end
      endgenerate
    end

      default: state_next = IDLE; 
    endcase
  end // always_comb

  always_comb begin : output
    q_o   = 'b0;
    stb_o = 'b0;

    if (cnt >= OUTPUT) begin
      stb_o = 'b1;
      generate
        for (i = INPUT; i < 2*INPUT; i++) begin
          if (i - cnt == 'b0) begin
            q_o = cache[i*8-1:(i-INPUT)*8]
          end
        end
      endgenerate
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