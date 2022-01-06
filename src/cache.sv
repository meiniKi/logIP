/*
 * file: cache.sv
 * usage: 
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module cache #(
  parameter INPUT=4,                          //! number of input bytes
  parameter OUTPUT=4                          //! number of output bytes
) (                  
  input  logic                    clk_i,      //! system clock 
  input  logic                    rst_in,     //! system reset, low active
  input  logic                    cfg_stb_i,  //! configure flag, configuration at cfg_i is valid
  input  logic [INPUT-1:0]        cfg_i,      //! configure active input bytes
  input  logic                    stb_i,      //! indicates that input is ready
  input  logic [INPUT-1:0][7:0]   d_i,        //! input data
  output logic                    stb_o,      //! output is ready
  output logic [OUTPUT-1:0][7:0]  q_o         //! output data
);

  logic [INPUT+OUTPUT-2:0][7:0]     cache;
  logic [INPUT+OUTPUT-2:0][7:0]     cache_next;
  logic [INPUT-1:0]                 cfg;
  logic [$clog2(INPUT+OUTPUT)-1:0]  cnt;
  logic [$clog2(INPUT+OUTPUT)-1:0]  cnt_next;

  always_comb begin : caching
    cache_next      = cache;
    cnt_next        = cnt;
    
    if (cnt_next >= OUTPUT) begin
      cnt_next    = cnt - OUTPUT;
    end
    if (stb_i) begin
      for (integer i = INPUT-1; i >= 0; i--) begin
        if (~cfg[i]) begin
          cnt_next      = cnt_next + 1;
          cache_next    = cache_next << 8;
          cache_next[0] = d_i[i];
        end
      end
    end

  end // always_comb

  always_comb begin : assign_output
    q_o   = 'b0;
    stb_o = 'b0;

    if (cnt >= OUTPUT) begin
      stb_o = 'b1;
      q_o = cache[(cnt-1)-:OUTPUT];
    end
  end // always_comb

  always_ff @(posedge clk_i ) begin
    if (~rst_in) begin
      cache     <= 'b0;
      cnt       <= 'b0;
      cfg       <= 'b0;  
    end else begin
      cache     <= cache_next;
      cnt       <= cnt_next;
      if (cfg_stb_i) begin
        cfg <= cfg_i;     
      end
    end
  end // always_ff

endmodule