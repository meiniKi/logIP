/*
 * file: logIP_pkg.sv
 *
 */

package logIP_pkg;

  typedef enum logic [7:0] {
    /* TODO: optimize with don't care */
    CMD_S_SOFT_RESET          = 8'b0000_0000,
    CMD_S_RUN                 = 8'b0000_0001,
    CMD_S_ID                  = 8'b0000_0010,
    CMD_S_XON                 = 8'b0001_0001,
    CMD_S_XOFF                = 8'b0001_0011,
    CMD_L_MSK_SET_TRG_MSK     = 8'b1100_??00,
    CMD_L_MSK_SET_TRG_VAL     = 8'b1100_??01,
    CMD_L_MSK_SET_TRG_CONF    = 8'b1100_??10,
    CMD_L_MSK_SET_DIV         = 8'b1000_0000,
    CMD_L_MSK_SET_RD_DLY_CNT  = 8'b1000_0001,
    CMD_L_MSK_SET_FLAGS       = 8'b1000_0010 } opcode_t;

  typedef enum logic {XON, XOFF} xcrtl_t;
    
endpackage



