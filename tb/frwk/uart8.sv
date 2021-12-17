/*
 * file: uart8.sv
 * usage: Uart Transmitter+Receiver for standard 8 bit transmissions
 *        1  start  bit
 *        1  stop   bit
 *        no parity bit 
 */

`include "declarations.svh"
`include "uart8.svh"

class Uart8;
  mxb_uart_t  mbx_rx;
  mxb_uart_t  mbx_tx;
  time        bit_delay;

  function new(time bit_delay);
    this.bit_delay = bit_delay;
    this.mbx_rx = new();
    this.mbx_tx = new();
  endfunction

  task queue(input uart_item_t b);
    this.mbx_tx.put(b);
  endtask

  task _transmit(input logic [7:0] b, ref logic tx);
    #(bit_delay) tx = 'b0;
    repeat(8) begin
      #(bit_delay) tx = b[0];
      b >>= 1;
    end
    #(bit_delay) tx = 'b1;
  endtask

  task run_transmitter(ref logic tx);
    uart_item_t t;
    tx = 'b1;
    #100; // give time to init dut
    forever begin
      this.mbx_tx.get(t);
      this._transmit(t, tx);
    end
  endtask

  /* TODO continue
  task run_receiver(ref logic rx);
    logic [7:0] r;
    while (rx);
    #(3 * bit_delay/2);
    repeat(8) begin
      r[-1] = rx;
      r >>= 1;
      #(bit_delay);
    end
    #(bit_delay); // 1/2 bit_delay buffer to not re-trigger
    this.mbx_rx.put(byte'(t));
  endtask
  */


endclass