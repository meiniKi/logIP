# Package: logIP_pkg 

- **File**: logIP_pkg.sv
## Types

| Name     | Type                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Description |
| -------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------- |
| opcode_t | enum logic [7:0] {<br><span style="padding-left:20px">     /* TODO: optimize with don't care */                //     CMD_S_SOFT_RESET          = 8'b0000_0000,<br><span style="padding-left:20px">                          //     CMD_S_RUN                 = 8'b0000_0001,<br><span style="padding-left:20px">                //     CMD_S_ID                  = 8'b0000_0010,<br><span style="padding-left:20px">                               //                         //                                                                      //     CMD_OLS_QUERY_META_DATA   = 8'b0000_0100,<br><span style="padding-left:20px">                     //     CMD_OLS_FINISH_NOW        = 8'b0000_0101,<br><span style="padding-left:20px">                //     CMD_OLS_QUERY_INPUT_DATA  = 8'b0000_0110,<br><span style="padding-left:20px">                     //     CMD_OLS_ARM_ADV_TRG       = 8'b0000_1111,<br><span style="padding-left:20px">                //     CMD_S_XON                 = 8'b0001_0001,<br><span style="padding-left:20px">                //     CMD_S_XOFF                = 8'b0001_0011,<br><span style="padding-left:20px">                                              //     CMD_L_MSK_SET_DIV         = 8'b1000_0000,<br><span style="padding-left:20px">                //               //               //     CMD_L_MSK_SET_RD_DLY_CNT  = 8'b1000_0001,<br><span style="padding-left:20px">                     //                                                                                                                        //          //                                                                 CMD_L_MSK_SET_FLAGS       = 8'b1000_0010,<br><span style="padding-left:20px">           //          //               CMD_OLS_ADV_TRG_CONG      = 8'b1001_1110,<br><span style="padding-left:20px">                     //          //     CMD_OLS_ADV_TRG_DATA      = 8'b1001_1111,<br><span style="padding-left:20px">                               //          //     CMD_L_MSK_SET_TRG_MSK     = 8'b1100_??00,<br><span style="padding-left:20px">                          //          //     CMD_L_MSK_SET_TRG_VAL     = 8'b1100_??01,<br><span style="padding-left:20px">                     //                                             //                    //                                             //     CMD_L_MSK_SET_TRG_CONF    = 8'b1100_??10 } |             |
| xcrtl_t  | enum logic {<br><span style="padding-left:20px">XON,<br><span style="padding-left:20px"> XOFF}                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            |             |