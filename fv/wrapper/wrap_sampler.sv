/*
 * file: wrap_sampler.sv
 * usage: Wrapper for sampler.sv for formal.
 *
 */

module top_sampler #(parameter CHLS=32)(
  // General
  input  logic            clk_i,      //! system clock
  input  logic            rst_in,     //! system reset, low active
  // Config
  input  logic [23:0]     fdiv_i,     //! new division factor, part of cmd
  input  logic            set_div_i,  //! flag to update division factor
  // Data IO
  input  logic [CHLS-1:0] data_i,     //! input channels
  output logic [CHLS-1:0] smpls_o,    //! sampled input channels
  output logic            stb_o       //! flag took sample        
  );

  sampler i_sampler( .* );

endmodule