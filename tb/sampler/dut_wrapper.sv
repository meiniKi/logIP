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

module dut_wrapper(dut_if.duv ifc);
sampler #(.CHLS(32)) dut (  .clk_i          (ifc.clk_i),
                            .rst_in         (ifc.rst_in),
                            .fdiv_i         (ifc.fdiv_i),
                            .set_div_i      (ifc.set_div_i),
                            .data_i         (ifc.data_i),
                            .smpls_o        (ifc.smpls_o),
                            .stb_o          (ifc.stb_o));
endmodule