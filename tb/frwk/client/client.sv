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

  task set_trigger_mask(int stage, int value);
    logic [31:0]  val = value;
    logic [7:0]   opc = CMD_L_MSK_SET_TRG_MSK;
                  opc[3:2] = stage;
    i_uart8.transmit_cmd({opc, val});
  endtask

  task set_trigger_value(int stage, int value);
    logic [31:0]  val = value;
    logic [7:0]   opc = CMD_L_MSK_SET_TRG_VAL;
                  opc[3:2] = stage;
    i_uart8.transmit_cmd({opc, val});
  endtask


  // TODO append

endclass