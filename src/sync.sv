/*
 * file: sync.sv
 * usage: Synchronizer of async signals by two FFs.
 */

`default_nettype none
module sync #(parameter WIDTH) (
                                  input  logic              clk_i,
                                  input  logic              rst_in,
                                  input  logic [WIDTH-1:0]  async_i,
                                  output logic [WIDTH-1:0]  sync_o);

logic [WIDTH-1:0] inter;
                                  
always_ff @(posedge clk) begin
  if (rst_in == 'b0) begin
    inter   <= 'b0;
    sync_o  <= 'b0;
  end else begin
    inter   <= async_i;
    sync_o  <= inter;
  end
end

endmodule