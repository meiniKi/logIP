/*
 * file: client.sv
 * usage: Simulated SUMP/OLS client
 */

class Client;
  Uart8       i_uart8;

  import logIP_pkg::*;

  function new(Uart8 i_uart8);
    this.i_uart8 = i_uart8;
  endfunction

  task query_id();
    i_uart8.transmit(byte'(CMD_S_ID));
  endtask

  // TODO append

endclass