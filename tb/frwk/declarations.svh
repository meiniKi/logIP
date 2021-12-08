/*
 * file: declarations.sv
 * usage: 
 * 
 */

`ifndef H_DECLARATIONS
`define H_DECLARATIONS

typedef enum logic [1:0] { SCORE_PASS, SCORE_FAIL, SCORE_DONE } score_t;
typedef mailbox #(score_t) score_mbox_t;

`endif