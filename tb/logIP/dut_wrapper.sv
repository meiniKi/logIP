/*
 * file: dut_wrapper.sv
 * 
 */

`default_nettype wire
`timescale 1ns/1ps

module dut_wrapper(dut_if.duv ifc);
logIP #(.CHLS(32),
        .UART_CLK_PER_BIT(3)) dut ( 
            .clk_i    (ifc.clk_i),
            .rst_in   (ifc.rst_in),
            .chls_i   (ifc.chls_i),
            .rx_i     (ifc.rx_i),
            .tx_o     (ifc.tx_o));
endmodule