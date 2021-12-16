


module top_lutram #( parameter WIDTH = 32,
                     parameter DEPTH = 4) (
  input  logic                      clk_i,    //! system clock
  input  logic                      rst_in,   //! system reset
  input  logic                      en_i,     //! enable
  input  logic                      we_i,     //! write enable (read / write)
  input  logic [DEPTH-1:0]          addr_i,   //! address
  input  logic [WIDTH-1:0]          d_i,      //! data in
  output logic [WIDTH-1:0]          d_o       //! data out
);

lutram #( .WIDTH (WIDTH),
          .DEPTH (DEPTH)) i_lutram (
  .clk_i  (clk_i),
  .rst_in (rst_in),
  .en_i   (en_i),
  .we_i   (we_i),
  .addr_i (addr_i),
  .d_i    (d_i),
  .d_o    (d_o)
);

endmodule