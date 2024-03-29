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
 * file: sampler.sv
 * usage: Takes samples at specified sampling frequency.
 *
 */

`default_nettype wire
`timescale 1ns/1ps
module sampler #(localparam CHLS=32)(
  // General
  input  logic            clk_i,      //! system clock
  input  logic            rst_in,     //! system reset, low active
  // Config
  input  logic [23:0]     fdiv_i,     //! new division factor, part of cmd
  input  logic            set_div_i,  //! flag to update division factor
  input  logic            exec_i,
  // Data IO
  input  logic [CHLS-1:0] data_i,     //! input channels
  output logic [CHLS-1:0] smpls_o,    //! sampled input channels
  output logic            stb_o       //! flag took sample        
  );

  // Stored frequency division factor
  //
  logic [23:0] r_div;

  // Counter to divide system frequency
  //
  logic [23:0] cnt;

  // Capture of input channels
  //
  logic [CHLS-1:0] r_smpls;

  assign smpls_o = r_smpls;

  always_ff @(posedge clk_i) begin : take_samples
    if (~rst_in) begin
      cnt       <= 'b0;
      stb_o     <= 'b0;
    end else begin
      if (cnt < r_div) begin
        cnt     <= cnt + 'b1;
        stb_o   <= 'b0;
      end else begin
        cnt     <= 'b0;
        r_smpls <= data_i;
        stb_o   <= 'b1;
      end
    end
  end // always_ff


  always_ff @(posedge clk_i) begin : set_fdiv
    if (~rst_in) begin
      r_div <= 'b0;
    end else if (set_div_i & exec_i) begin
      r_div <= fdiv_i;
    end
  end // always_ff


`ifdef FORMAL
  logic f_init = 0;

  always_ff @(posedge clk_i) begin : f_initial_reset
    if (!f_init) begin
      assume (rst_in == 0);
      f_init = 1;
    end
  end

  // TODO: FIX
  always_ff @(posedge clk_i) begin
    if (rst_in) begin
      // assume flag only high one tick
      if (set_div_i)
        assume (!$past(set_div_i));

      if ($rose(stb_o))     assert property (!$past(stb_o));
      if ($fell(stb_o))     assert property ($past(stb_o));
      //if ($rose(stb_o))     assert property (smpls_o == data_i);
      if ($rose($past(set_div_i))) assert property (fdiv_i == r_div);
    end
  end

`endif

endmodule // sampler
