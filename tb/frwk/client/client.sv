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
    i_uart8.transmit_cmd(opc, val);
  endtask

  task set_flags(int value);
    logic [31:0]  val = value;
    logic [7:0]   opc = CMD_L_MSK_SET_FLAGS;
    i_uart8.transmit_cmd(opc, val);
  endtask

  task set_trigger_value(int stage, int value);
    logic [31:0]  val = value;
    logic [7:0]   opc = CMD_L_MSK_SET_TRG_VAL;
                  opc[3:2] = stage;
    i_uart8.transmit_cmd(opc, val);
  endtask

  task set_sampling_rate(longint f_sys, longint f_smpl);
    logic [23:0]  div = f_sys/f_smpl - 'b1;
    i_uart8.transmit_cmd(CMD_L_MSK_SET_DIV, {8'h0, div});
  endtask

  task set_count_samples(int read_count_nr, int delay_count_nr);
    logic [15:0]  r_cnt = read_count_nr;
    logic [15:0]  d_cnt = delay_count_nr;
    i_uart8.transmit_cmd(CMD_L_MSK_SET_RD_DLY_CNT, {d_cnt, r_cnt});
  endtask

  task set_stage_config(logic stage, logic start);
    // TODO: include other flags
    logic [7:0]   opc = CMD_L_MSK_SET_TRG_CONF;
                  opc[3:2] = stage;
    i_uart8.transmit_cmd(opc, {4'b0, start, 27'b0});
  endtask

  task reset();
    i_uart8.transmit('b0);
    i_uart8.transmit('b0);
    i_uart8.transmit('b0);
    i_uart8.transmit('b0);
    i_uart8.transmit('b0);
  endtask

  task run();
    i_uart8.transmit(byte'(CMD_S_RUN));
  endtask


  // TODO append

endclass