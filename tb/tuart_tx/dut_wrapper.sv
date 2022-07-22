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
tuart_tx #( .WORD_BITS (8),
            .CMD_WORDS (4),
            .CLK_PER_SAMPLE (05)) dut ( .clk_i    (ifc.clk_i),
                                        .rst_in   (ifc.rst_in),
                                        .stb_i    (ifc.stb_i),
                                        .rdy_o    (ifc.rdy_o),
                                        .tx_o     (ifc.tx_o),
                                        .xstb_i   (ifc.xstb_i),
                                        .xoff_i   (ifc.xoff_i),
                                        .xon_i    (ifc.xon_i),
                                        .data_i   (ifc.data_i),
                                        .sel_i    (ifc.sel_i));
endmodule