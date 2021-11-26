/*
 * file: syncro.sv
 * usage: Synchronizer of async signals by two FFs.
 */

`default_nettype wire
module syncro #(parameter WIDTH = 1,
                parameter INIT_VAL = 1) (
                                    input  logic              clk_i,
                                    input  logic              rst_in,
                                    input  logic [WIDTH-1:0]  async_i,
                                    output logic [WIDTH-1:0]  sync_o);

logic [WIDTH-1:0] inter;
                                  
always_ff @(posedge clk_i) begin
  if (rst_in == 'b0) begin
    inter   <= INIT_VAL;
    sync_o  <= INIT_VAL;
  end else begin
    inter   <= async_i;
    sync_o  <= inter;
  end
end

endmodule