/*
 * file: core.sv
 * usage: 
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module core #(
  parameter DEPTH=5                         //! memory depth / address width
) (           
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  
  input  logic [39:0]           cmd_i,      //! command data
  input  logic [WIDTH-1:0]      input_i,    //! input to sample
  input  logic                  tx_rdy_i,   //! transmitter ready flag
  input  logic [WIDTH-1:0]      mem_i,      //! input from memory
  input  logic                  exec_i,     //! execute command
  output logic                  rst_o,      //! reset flag
  output logic                  we_o,       //! write enable
  output logic [DEPTH-1:0]      addr_o,     //! memory address
  output logic [WIDTH-1:0]      mem_o,      //! output to memory
  output logic                  tx_stb_o,   //! starts transmitter
  output logic [WIDTH-1:0]      tx_o        //! data for the transmitter to send
);

  localparam WIDTH = 32;

  logic                   rst;
  logic                   sft_rst;
  logic                   arm;
  logic                   set_mask;
  logic                   set_val;
  logic                   set_cfg;
  logic                   set_div;
  logic                   set_cnt;
  logic                   set_flgs;
  logic [1:0]             stg;
  logic                   xstb;
  logic                   xon;
  logic                   xoff;
  logic [WIDTH-1:0]       smpls;
  logic                   smpls_stb;
  logic                   run;
  logic                   we;
  logic [DEPTH-1:0]       addr;
  logic [WIDTH-1:0]       mem_w;
  logic [WIDTH-1:0]       mem_r;

  assign rst   = ~sft_rst && rst_in;
  assign rst_o = rst;

  indec i_indec (
    .clk_i(clk_i),          
    .rst_in(rst),         
    .stb_i(exec_i),          
    .opc_i(cmd_i[39:32]),          
    .sft_rst_o(sft_rst),      
    .arm_o(arm),          
    //.id_o(),                // Not yet used   
    .set_mask_o(set_mask),     
    .set_val_o(set_val),      
    .set_cfg_o(set_cfg),      
    .set_div_o(set_div),      
    .set_cnt_o(set_cnt),      
    .set_flgs_o(set_flgs),     
    .stg_o(stg), 
    //.stb_o(),               // Not yet used    
    .xstb_o(xstb),         
    .xon_o(xon),          
    .xoff_o(xoff)        
    //.rd_meta_o(),           // Not yet used    
    //.fin_now_o(),           // Not yet used    
    //.rd_inp_o(),            // Not yet used    
    //.arm_adv_o(),           // Not yet used    
    //.set_adv_cfg_o(),       // Not yet used    
    //.set_adv_dat_o()        // Not yet used    
  );

  sampler i_sampler (
    .clk_i(clk_i),
    .rst_in(rst),
    .fdiv_i(cmd_i[31:8]),
    .set_div_i(set_div),
    .data_i(input_i),
    .smpls_o(smpls),
    .stb_o(smpls_stb)
  );

  trigger i_trigger (
    .clk_i(clk_i),     
    .rst_in(rst),    
    .cmd_i(cmd_i[31:0]),     
    .stg_i(stg),     
    .set_mask_i(set_mask),
    .set_val_i(set_val), 
    .set_cfg_i(set_cfg), 
    .arm_i(arm),     
    .stb_i(smpls_stb),     
    .smpls_i(smpls),   
    .run_o(run)  
  );

  ctrl i_ctrl (
    .clk_i(clk_i),     
    .rst_in(rst),    
    .set_cnt_i(set_cnt), 
    .cmd_i(cmd_i[31:0]),     
    .run_i(run),     
    .stb_i(smpls_stb),     
    .smpls_i(smpls),   
    .d_i(mem_r),       
    .tx_rdy_i(tx_rdy_i),  
    .we_o(we),      
    .addr_o(addr),    
    .q_o(mem_w),       
    .tx_stb_o(tx_stb_o),  
    .tx_o(tx_o)
  );

  ramif #(
    .DEPTH(DEPTH)
  ) i_ramif (
    .clk_i(clk_i),    
    .rst_in(rst),   
    .en_i('b1),     
    .we_i(we),     
    .addr_i(addr),   
    .d_i(mem_w),      
    .q_o(mem_r)     
  );

endmodule