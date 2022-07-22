/* Copyright (C) 2021-2022 Meinhard Kissich
 * Copyright (C) 2021-2022 Klaus Weinbauer
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 *
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

`define SCORE_ASSERT_STR(ARG, STR) \
  #0 assert(ARG) mbx.put(score_t'(0)); else begin mbx.put(score_t'(1)); $display("[ERROR] %s @ %t", STR, $time); end

`define SCORE_DONE \
  mbx.put(score_t'(2));

// Vivado does not support the _cycle delay_ (##x).
// This is used as a workaround.
//
`define WAIT_CYCLES(NR, CLK) \
  repeat(NR) @(posedge CLK);

// Higher level assertions that use the basic ones
//
`define ASSERT_EQ_STR(EXP, ACT, STR) \
  if (EXP != ACT) \
    $display("[ERROR] %t | Expected value 0x%h but got 0x%h.", $time, EXP, ACT); \
  `SCORE_ASSERT_STR(EXP == ACT, STR);

`define ASSERT_EQ(expected, actual) \
  if (expected != actual) \
    $display("[ERROR] %t | Expected value 0x%h but got 0x%h.", $time, expected, actual); \
  `SCORE_ASSERT(expected == actual);



`endif