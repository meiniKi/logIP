/*
 * file: core.sv
 * usage: 
 *
 */

`default_nettype wire
`timescale 1ns/1ps

module core #(
  parameter  DEPTH =  5,                    //! memory depth / address width
  localparam WIDTH = 32                     // here, to be used in portlist
) (           
  // General            
  input  logic                  clk_i,      //! system clock 
  input  logic                  rst_in,     //! system reset, low active
  input  logic [WIDTH-1:0]      input_i,    //! input to sample
  // Receive
  input  logic [ 7:0]           opc_i,      //! opcpde 
  input  logic [31:0]           cmd_i,      //! command data
  input  logic                  exec_i,     //! execute command
  // Memory interface
  output logic                  we_o,       //! write enable
  output logic [DEPTH-1:0]      addr_o,     //! memory address
  input  logic [WIDTH-1:0]      mem_i,      //! input from memory
  output logic [WIDTH-1:0]      mem_o,      //! output to memory
  // Transmit
  input  logic                  tx_rdy_i,   //! transmitter ready flag
  output logic                  tx_stb_o,   //! starts transmitter
  output logic [WIDTH-1:0]      tx_o,       //! data for the transmitter to send
  output logic                  tx_xon_o,   //! transmitter flow control on
  output logic                  tx_xoff_o   //! transmitter flow control on
);

  logic               rst_n;
  logic               sft_rst;

  logic               arm;
  logic               id;
  logic               set_mask;
  logic               set_val;
  logic               set_cfg;
  logic               set_div;
  logic               set_cnt;
  logic               set_flgs;
  logic [1:0]         stg;
  logic [WIDTH-1:0]   smpls;
  logic               smpls_stb;
  logic               run;

  logic               tx_stb_from_rdback;
  logic               tx_stb_from_ctrl;
  logic               tx_sel_ram;
  logic [WIDTH-1:0]   tx_from_ram;
  logic [WIDTH-1:0]   tx_from_rdback;

  // Connect data from the ram to the output when the
  // controller wants to report samples back to the client
  // otherwise, data from rdback can write back
  //
  assign tx_o = tx_sel_ram ? tx_from_ram : tx_from_rdback;

  // Theoretically, the strobe signals can be or'ed together,
  // as reading back configuration data and transmission of
  // samples to the client don't overlap. However, priority
  // is given to writing back samples if a client requests 
  // data while writing back samples.
  //
  assign tx_stb_o = tx_sel_ram ? tx_stb_from_ctrl : tx_stb_from_rdback;

  // Assignments kept to consider 'fake-RLE' here: Load/Store like
  // RLE, but sent to the client as without RLE
  //
  assign mem_o        = smpls;
  assign tx_from_ram  = mem_i;

  // Be careful of glitches here
  //
  assign rst_n        = rst_in & (~(sft_rst & exec_i));

  indec i_indec (
    .clk_i            (clk_i),          
    .rst_in           (rst_n),         
    .stb_i            (exec_i),          
    .opc_i            (opc_i),          
    .sft_rst_o        (sft_rst),      
    .arm_o            (arm),          
    .id_o             (id),
    .set_mask_o       (set_mask),     
    .set_val_o        (set_val),      
    .set_cfg_o        (set_cfg),      
    .set_div_o        (set_div),      
    .set_cnt_o        (set_cnt),      
    .set_flgs_o       (set_flgs),     
    .stg_o            (stg),       
    .xon_o            (tx_xon_o),          
    .xoff_o           (tx_xoff_o)        
    //.rd_meta_o        (),         // Not yet used    
    //.fin_now_o        (),         // Not yet used    
    //.rd_inp_o         (),         // Not yet used    
    //.arm_adv_o        (),         // Not yet used    
    //.set_adv_cfg_o    (),         // Not yet used    
    //.set_adv_dat_o    ()          // Not yet used    
  );

  sampler i_sampler (
    .clk_i      (clk_i),
    .rst_in     (rst_n),
    .fdiv_i     (cmd_i[23:0]),
    .set_div_i  (set_div),
    .data_i     (input_i),
    .smpls_o    (smpls),
    .stb_o      (smpls_stb)
  );

  trigger i_trigger (
    .clk_i      (clk_i),     
    .rst_in     (rst_n),    
    .cmd_i      (cmd_i),     
    .stg_i      (stg),     
    .set_mask_i (set_mask),
    .set_val_i  (set_val), 
    .set_cfg_i  (set_cfg), 
    .arm_i      (arm),     
    .stb_i      (smpls_stb),     
    .smpls_i    (smpls),   
    .run_o      (run)  
  );

  ctrl i_ctrl (
    .clk_i      (clk_i),     
    .rst_in     (rst_n),    
    .set_cnt_i  (set_cnt), 
    .cmd_i      (cmd_i),
    .run_i      (run),     
    .stb_i      (smpls_stb),            
    .we_o       (we_o),      
    .addr_o     (addr_o),       
    .tx_rdy_i   (tx_rdy_i),   
    .tx_stb_o   (tx_stb_from_ctrl),
    .tx_sel_o   (tx_sel_ram)
  );

  rdback i_rdback (           
    .clk_i      (clk_i),       
    .rst_in     (rst_n),
    .exec_i     (exec_i),
    .tx_rdy_i   (tx_rdy_i),
    .id_i       (id),
    //.rd_meta_i  (),               // Not yet used 
    .tx_o       (tx_from_rdback),       
    .stb_o      (tx_stb_from_rdback)
  );

endmodule