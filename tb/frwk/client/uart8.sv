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
  bit         tx_done;
  // Todo: possible to store 'ref logic tx' as class member?

  function new(time bit_delay);
    this.bit_delay  = bit_delay;
    this.mbx_rx     = new();
    this.mbx_tx     = new();
  endfunction

  // Note: Be aware of the transmit order.
  //
  task transmit_cmd(input logic [7:0] opc, input logic [31:0] c);
    this.transmit(uart_item_t'(opc));
    this.transmit(uart_item_t'(c[7:0]));
    this.transmit(uart_item_t'(c[15:8]));
    this.transmit(uart_item_t'(c[23:16]));
    this.transmit(uart_item_t'(c[31:24]));
  endtask

  task transmit(input uart_item_t b);
    this.mbx_tx.put(b);
  endtask

  // More efficient than querying in the
  // tester each system clock tick
  task wait_transmit_done();
    while (!this.is_transmit_done()) #this.bit_delay;
  endtask

  function is_transmit_done();
    return this.mbx_tx.num() == 0;
  endfunction

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
      // Pop the element after tx is finished
      // to use the queue count for is_transmit_done().
      //
      this.mbx_tx.peek(t);
      this._transmit(t, tx);
      // ensure to have rx read in feedback loop
      #bit_delay;
      this.mbx_tx.get(t);
    end
  endtask

  task run_receiver(ref logic rx);
    logic [7:0] r = 'b0;
    #90;
    forever begin
      @(negedge rx);
      #(3 * bit_delay/2);
      repeat(8) begin
        r >>= 1;
        r[7] = rx;
        #(bit_delay);
      end
      #(bit_delay/2);
      this.mbx_rx.put(byte'(r));
    end
  endtask


endclass