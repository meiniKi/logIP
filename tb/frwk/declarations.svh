/*
 * file: declarations.sv
 * usage: 
 * 
 */

`ifndef H_DECLARATIONS
`define H_DECLARATIONS

typedef enum logic [1:0] { SCORE_PASS=0, SCORE_FAIL=1, SCORE_DONE=2 } score_t;
typedef mailbox #(score_t) score_mbox_t;

`define SCORE_ASSERT(ARG) \
  #0 assert(ARG) mbx.put(score_t'(0)); else mbx.put(score_t'(1));

`define SCORE_ASSERT_LBL(ARG, LBL) \
  #0 assert(ARG) mbx.put(score_t'(0)); else begin mbx.put(score_t'(1)); $display(LBL); end
  

`define SCORE_DONE \
  mbx.put(score_t'(2));

// Vivado does not support the _cycle delay_ (##x).
// This is used as a workaround.
//
`define WAIT_CYCLES(NR, CLK) \
  repeat(NR) @(posedge CLK);

`endif