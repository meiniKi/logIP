/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
mmu dut ( .clk_i          (ifc.clk_i),
          .rst_in         (ifc.rst_in),
          .wrt_i          (ifc.wrt_i),  
          .read_i         (ifc.read_i), 
          .d_i            (ifc.d_i),      
          .d_o            (ifc.d_o));
endmodule