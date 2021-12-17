/*
 * file: syncro.sv
 * usage: Synchronizer of async signals by two FFs.
 */

`default_nettype wire
module syncro #(
  parameter WIDTH = 32,                 //! signal width
  parameter INIT_VAL = 'b0              //! initial value
) (
  input  logic              clk_i,      //! system clock 
  input  logic              rst_in,     //! system reset, low active
  input  logic [WIDTH-1:0]  async_i,    //! asynchronous input
  output logic [WIDTH-1:0]  sync_o      //! synchronized output
);

  logic [WIDTH-1:0] inter;

  assign sync_o = inter;

  always_ff @(posedge clk_i) begin
    if (rst_in == 'b0) begin
      inter   <= INIT_VAL;
    end else begin
      inter   <= async_i;
    end
  end

endmodule