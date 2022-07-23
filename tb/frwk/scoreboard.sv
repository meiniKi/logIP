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
 * file: scoreboard.sv
 * usage: 
 * 
 */
`include "declarations.svh"
class Scoreboard;

  int checks;
  int fails;

  score_mbox_t mbx;

  function new(score_mbox_t mbx);
    this.checks = 0;
    this.fails  = 0;
    this.mbx    = mbx;
  endfunction

  function void add_fail();
    this.checks++;
    this.fails++;
  endfunction

  function void add_pass();
    this.checks++;
  endfunction
  
  function void print_score();
    $display("===========================================");
    $display("Performed Checks    = %0d", this.checks);
    $display("Failed Checks       = %0d", this.fails);
    $display("===========================================");
  endfunction

  task run();
    check_mailbox();
  endtask

  task check_mailbox();
    score_t sc;

    do begin
    
      mbx.get(sc);

      if (sc == SCORE_PASS)
        add_pass();
      else if (sc == SCORE_FAIL)
        add_fail();

    end while (sc != SCORE_DONE);
    print_score();

  endtask
endclass