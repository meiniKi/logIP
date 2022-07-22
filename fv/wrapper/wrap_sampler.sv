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
 * file: wrap_sampler.sv
 * usage: Wrapper for sampler.sv for formal.
 *
 */

module top_sampler #(parameter CHLS=32)(
  // General
  input  logic            clk_i,      //! system clock
  input  logic            rst_in,     //! system reset, low active
  // Config
  input  logic [23:0]     fdiv_i,     //! new division factor, part of cmd
  input  logic            set_div_i,  //! flag to update division factor
  // Data IO
  input  logic [CHLS-1:0] data_i,     //! input channels
  output logic [CHLS-1:0] smpls_o,    //! sampled input channels
  output logic            stb_o       //! flag took sample        
  );

  sampler i_sampler( .* );

endmodule