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
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if ifc);

  ctrl #( .DEPTH(5)) dut (.clk_i      (ifc.clk_i),
                          .rst_in     (ifc.rst_in),
                          .set_cnt_i  (ifc.set_cnt_i),
                          .cmd_i      (ifc.cmd_i),
                          .run_i      (ifc.run_i),
                          .stb_i      (ifc.stb_i),
                          .we_o       (we_o),
                          .addr_o     (addr_o),
                          .tx_rdy_i   (ifc.tx_rdy_i),
                          .tx_stb_o   (ifc.tx_stb_o),
                          .tx_sel_o   (ifc.tx_sel_o)
  );
endmodule