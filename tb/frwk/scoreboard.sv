/*
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