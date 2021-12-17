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
  // Todo: possible to store 'ref logic tx' as class member?

  function new(time bit_delay);
    this.bit_delay = bit_delay;
    this.mbx_rx = new();
    this.mbx_tx = new();
  endfunction

  task transmit(input uart_item_t b);
    this.mbx_tx.put(b);
  endtask

  function is_receive_empty();
    return this.mbx_rx.num() == 0;
  endfunction

  task receive(output uart_item_t r);
    this.mbx_rx.get(r);
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

  task run_receiver(ref logic rx);
    logic [7:0] r = 'b0;
    #90;
    @(negedge rx);
    #(3 * bit_delay/2);
    repeat(8) begin
      r >>= 1;
      r[7] = rx;
      #(bit_delay);
    end
    #(bit_delay); // 1/2 bit_delay buffer
    this.mbx_rx.put(byte'(r));
  endtask


endclass