/*
 * file: cache.sv
 * usage: Keep memory interface at constant width even when
 *        some of the channels are disabled.
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module cache (                  
  input  logic              clk_i,      //! system clock 
  input  logic              rst_in,     //! system reset, low active
  input  logic              cfg_stb_i,  //! configure flag, configuration at cfg_i is valid
  input  logic [3:0]        cfg_i,      //! configure active input bytes
  input  logic              stb_i,      //! indicates that input is ready
  input  logic [3:0][7:0]   d_i,        //! input data
  output logic              stb_o,      //! output is ready
  output logic [3:0][7:0]   q_o         //! output data
);

  states_t state;
  states_t state_next;

  // Register to build 
  // 

  logic [7:0] [7:0]                 cache;
  logic [7:0] [7:0]                 cache_next;

  logic [3:0]                       cfg;

  logic [$clog2($bits(cfg)+1)-1:0]  cfg_ones;

  logic                             store_bytes;
  logic [$clog2(8):0]               cnt;
  logic [$clog2(8):0]               cnt_new;

  logic A;
  logic B;
  logic C;
  logic D;

  assign A = cfg[3];
  assign B = cfg[3];
  assign C = cfg[3];
  assign D = cfg[3];

  assign cnt_new      = cnt + cfg;
  assign store_bytes  = cnt_new >= 'd4;
  assign stb_o        = store_bytes;
  assign q_o          = 'b0; // Todo: continue


  always_comb begin : number_bytes_to_add
    cfg_ones = '0;  
    foreach(cfg[idx]) begin
      cfg_ones += cfg[idx];
    end
  end // always_comb


  always_comb begin : caching
    // This is not beautiful but might be the best solution
    // without a huge increase in area
    //
    // A B C D || MUX3 | MUX2 | MUX1 | MUX0 |
    // 0 0 0 0 || x x  | x x  | x x  | x x  |
    // 0 0 0 1 || x x  | x x  | x x  | 0 0  |
    // 0 0 1 0 || x x  | x x  | x x  | 0 1  |
    // 0 0 1 1 || x x  | x x  | 0 1  | 0 0  |
    // 0 1 0 0 || x x  | x x  | x x  | 1 0  |
    // 0 1 0 1 || x x  | x x  | 1 0  | 0 0  |
    // 0 1 1 0 || x x  | x x  | 1 0  | 0 1  |
    // 0 1 1 1 || x x  | 1 0  | 0 1  | 0 0  | 
    // 1 0 0 0 || x x  | x x  | x x  | 1 1  |
    // 1 0 0 1 || x x  | x x  | 1 1  | 0 0  |
    // 1 0 1 0 || x x  | x x  | 1 1  | 0 1  |
    // 1 0 1 1 || x x  | 1 1  | 0 1  | 0 0  | 
    // 1 1 0 0 || x x  | x x  | 1 1  | 1 0  |
    // 1 1 0 1 || x x  | 1 1  | 1 0  | 0 0  |
    // 1 1 1 0 || x x  | 1 1  | 1 0  | 0 1  |
    // 1 1 1 1 || 1 1  | 1 0  | 0 1  | 0 0  |
    //
    //
    // MUX3 = {1, 1}
    // MUX2 = {1 ,~B|~C|~D}
    // MUX1 = {~C|~D, ~B|CD|~C~D}
    // MUX0 = {~C~D)|~ABCD, C~D|~B~D}
    //
    cache_next      <<= cfg_ones;
    cache_next[0]   = stb_i[{(~C&~D)|(~A&B&C&D), (C&~D)|(~B&~D)}];
    cache_next[1]   = stb_i[~C|~D, ~B|(C&D)|(~C&~D)];
    cache_next[2]   = stb_i[{'b1', ~B|~C|~D}];
    cache_next[3]   = stb_i[2'b11];
    

  end // always_comb


  always_ff @(posedge clk_i ) begin : fsm
    if (~rst_in) begin
      cnt       <= 'b0;
    end else if (stb_i) begin
      cnt       <= store_bytes ? cnt_new - 'd4 : cnt_new;
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