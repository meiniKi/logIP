/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
mmu dut ( .clk_i          (ifc.clk_i),
          .rst_in         (ifc.rst_in),
          .mem_wrt_i      (ifc.mem_wrt_i),  
          .mem_read_i     (ifc.mem_read_i), 
          .mem_i          (ifc.mem_i),      
          .mem_o          (ifc.mem_o));
endmodule