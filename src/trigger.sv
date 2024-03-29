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
 * file: trigger.sv
 * usage: Trigger unit
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module trigger #( parameter STAGES = 4) (
  // General
  input  logic              clk_i,      //! system clock
  input  logic              rst_in,     //! system reset, low active
  // Command and Flags
  input  logic [31:0]       cmd_i,      //! command
  input  logic [ 1:0]       stg_i,      //! stage
  input  logic              set_mask_i, //! flag, set trigger mask
  input  logic              set_val_i,  //! flag, set trigger value
  input  logic              set_cfg_i,  //! flag, set trigger configuration
  // Flow 
  input  logic              arm_i,      //! flag, arm trigger
  // Data
  input  logic              stb_i,      //! flag, new data samples
  input  logic [31:0]       smpls_i,    //! sampled channels
  // Output
  output logic              run_o       //! flag, trigger run
);

import logIP_pkg::*;

  logic [STAGES-1:0]   set_mask;
  logic [STAGES-1:0]   set_val;
  logic [STAGES-1:0]   set_cfg;
  logic [STAGES-1:0]   run;
  logic [STAGES-1:0]   match;

  logic [1:0]          r_lvl;

  assign run_o = |run;

  for (genvar i = 0; i < STAGES; i++) begin
    assign set_mask[i]  = stg_i == i ? set_mask_i : 'b0;
    assign set_val[i]   = stg_i == i ? set_val_i  : 'b0;
    assign set_cfg[i]   = stg_i == i ? set_cfg_i  : 'b0;

    stage i_stage (
      .clk_i      (clk_i),
      .rst_in     (rst_in),
      .cmd_i      (cmd_i),
      .set_mask_i (set_mask[i]),
      .set_val_i  (set_val[i]),
      .set_cfg_i  (set_cfg[i]),
      .arm_i      (arm_i),
      .stb_i      (stb_i),
      .smpls_i    (smpls_i),
      .lvl_i      (r_lvl),
      .match_o    (match[i]),
      .run_o      (run[i])
    );  
  end
    
  always_ff @(posedge clk_i) begin : fsm
    if (~rst_in || arm_i) begin
      r_lvl <= 'b0;
    end else begin 
      r_lvl <= |match ? r_lvl + 1 : r_lvl;
    end
  end

endmodule