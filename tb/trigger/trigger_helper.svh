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
 */

`ifndef H_TRIGGER_HELPER
`define H_TRIGGER_HELPER

`define CLK_DELAY `WAIT_CYCLES(1, clk_i)


`define SET_STAGE_VAL(STAGE, MASK, VALUES)      \
              duv_if.cb.cmd_i       <= MASK;    \
              duv_if.cb.stg_i       <= STAGE;   \
              duv_if.cb.set_mask_i  <= 'b1;     \
  `CLK_DELAY  duv_if.cb.set_mask_i  <= 'b0;     \
              duv_if.cb.cmd_i       <= VALUES;  \
              duv_if.cb.set_val_i   <= 'b1;     \
  `CLK_DELAY  duv_if.cb.set_val_i   <= 'b0


`define SET_STAGE_CONFIG(STAGE, DLY_L, DLY_H, CH_0_3, CH_4, LVL, START, SER) \
              duv_if.cb.cmd_i       <= {4'b0, START, SER, 1'b0, CH_4, CH_0_3, 2'b0, LVL, DLY_H, DLY_L}; \
              duv_if.cb.stg_i       <= STAGE; \
              duv_if.cb.set_cfg_i   <= 'b1;   \
  `CLK_DELAY  duv_if.cb.set_cfg_i   <= 'b0

`define SET_RESET \
  duv_if.cb.rst_in   <= 'b0;  \
  `CLK_DELAY                  \
  duv_if.cb.rst_in   <= 'b1

`define SET_ARMED \
  duv_if.cb.arm_i   <= 'b1;   \
  `CLK_DELAY                  \
  duv_if.cb.arm_i   <= 'b0





`endif
