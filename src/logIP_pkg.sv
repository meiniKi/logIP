/*
 * file: logIP_pkg.sv
 *
 */

package logIP_pkg;

  // Enable / Disable the OLS instruction set extension
  //
  `define P_OLS_EXTENSION_ENABLED

  // Select the type of RAM to synthesize the RAM
  //
  //`define USE_B_RAM
  `define USE_LUT_RAM


  // The supported instruction set.
  // Please refer to for the original description.
  // http://dangerousprototypes.com/docs/Logic_Analyzer_core:_Background
  //
  typedef enum logic [7:0] {
    /* TODO: optimize with don't care */

    // Clears stuck commands and resets the logic analyzer.
    // Shall be send at least five times.
    //
    CMD_S_SOFT_RESET          = 8'b0000_0000,

    // SUMP trigger start. Legacy command in OLS. 
    // It is used to trigger independent of trigger settings immediately. 
    // The device will sample _delay count_ samples and then return the 
    // buffer to the client.
    //
    CMD_S_RUN                 = 8'b0000_0001,

    // Responds the ID of the SUMP protocol.
    // Shall be "1ALS" ASCII encoded, LSB first.
    //
    CMD_S_ID                  = 8'b0000_0010,

    // Queries metadata of the logic analyzer core.
    // Token 0: end of meta data 
    // 0x01 - 0x1F: followed by NULL terminator
    // 0x20 - 0x3F: followed by uint32_t (MSB first)
    // 0x40 - 0x5F: followed by uint8_t
    //
    //  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    //  !! TODO: supported by fixed 32-bit TX module? !!
    //  !!       _len_ input required?                !!
    //  !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    //
    // Token   Description                         FPGA Currently Returns
    // -------------------------------------------------------------------
    // 0x00    End of Meta Data                    0
    // 0x01    Device Name                         "LogIP v0.1"
    // 0x02    Version of FPGA firmware            "0.1"
    // 0x03    Ancillary Version (PIC firmware)    -
    // 0x20    Number of Probes                    -
    // 0x21    Sample memory available (bytes)     24576 (parameterizable)
    // 0x22    Dynamic memory available (bytes)    -
    // 0x23    Maximum sample rate (Hz)            200000000 (parameterizable)
    // 0x24    Protocol version    -
    // 0x40    Number of Probes (short version)    32 (parameterizable)
    // 0x41    Protocol version (short version)    2
    //
    CMD_OLS_QUERY_META_DATA   = 8'b0000_0100,

    // Due to RLE, the buffer won't be filled when input samples are
    // not changing values. Subsequently, the sampling state will
    // not be left. This command forces the process of sampling.
    //
    CMD_OLS_FINISH_NOW        = 8'b0000_0101,

    // Four bytes snapshot of the latest sample of each
    // channel is transmitted.
    //
    CMD_OLS_QUERY_INPUT_DATA  = 8'b0000_0110,

    // Arm the advances trigger introduced by OLS.
    // Once it fires _delay count_ captures are taken.
    // Then, the whole buffer is transmitted.
    //
    CMD_OLS_ARM_ADV_TRG       = 8'b0000_1111,

    // Enables the UART transmitter to transmit
    // data on a strobe signal.
    //
    CMD_S_XON                 = 8'b0001_0001,

    // Disables the UART transmitter to transmit
    // data on a strobe signal.
    //
    CMD_S_XOFF                = 8'b0001_0011,

    // Sets the sampling rate by specifying a frequency
    // divider that scales the system clock.
    // 
    //      divider = (f_sys / f_smpl) - 1
    // 
    //   cmd = LSB ... MSB | 8'h??
    //         \----------/ \----/
    //           divider     dont care
    //
    CMD_L_MSK_SET_DIV         = 8'b1000_0000,

    // Sets the _Read-Count_ and the _Delay-Count_, the number of samples
    // captured by the logic analyzer.
    //
    // _Read-Count_:  (#samples)/4 captured and transmitted
    // _Delay-Count_: (#samples)/4 captured _after_ the trigger fires
    //
    // In case of _Read-Count_ > _Delay-Count_, the difference gives the
    // number of samples captures _before_ the trigger has fired.
    //
    CMD_L_MSK_SET_RD_DLY_CNT  = 8'b1000_0001,

    // Sets flags for features provided by the logic analyzer.
    // Flags marked with "x" are currently _not_ supported.
    // Flags marked with "~" will be supported in the next version.
    //
    // x    Demux Mode: 1=Enabled, double-data-rate capturing, shall only
    //                  be used at maximum sampling frequency.
    // x    Noise Filter Mode: 1=Enabled, reduces glitches on inputs.
    // x    Disable Channel Groups: 1=Disable group, Dont capture specific
    //                              groups of input data.
    // x    External Clock Source: 1=Enabled, uses an external sampling clock
    // x    Inverted External Capture Clock: 1=Enabled, sampled at falling edge
    //                                       of the external clock.
    // ~    RLE Compression: 1=Enabled, uses run-length-encoding to compress samples.
    //                       Most significant bit of sample is replaced by "rle-flag".
    //                       Client must be able to decode the compression.
    //                       _count_ is exclusive: <value><count=7> is equivalent to 8 times value.
    // x    Swap Number Scheme: 1=Enabled, swap upper and lower 16 bits of input.
    // x    External Test Mode: 1=Enabled, output 16-bit test pattern on channels [31:16].
    // x    Internal Test Mode: 1=Enabled, Apply internally generated 32 bit test 
    //                          pattern at sampling stage.
    // x    Extra RLE Compression Mode: Controls how often a <value> is stored to prevent 
    //                                  a buffer overflow in RLE mode when the input does
    //        Mode  Description         not change for a long time.
    //        ----------------------------------------------------------------------------
    //        0&1   Issue <value> & <rle-count> as pairs. Backwards compatible.   
    //        2     Periodic.  <values> reissed approx. every 256 <rle-count>.
    //        3     Unlimited. <values> can be followed by unlimited numbers of <rle-counts>.
    //
    //  cmd = | cmd_1 | cmd_0 | 8'h?? | 8'h??
    //
    //  cmd_1 [7]   : Inverted External Capture Clock
    //  cmd_1 [6]   : External Clock Source
    //  cmd_1 [5:2] : Disable Channel Groups 
    //  cmd_1 [1]   : Noise Filter Mode
    //  cmd_1 [0]   : Demux Mode
    //  cmd_0 [7:6] : Extra RLE Compression Mode
    //  cmd_0 [5:4] : dont cares 
    //  cmd_0 [3]   : Internal Test Mode
    //  cmd_0 [2]   : External Test Mode
    //  cmd_0 [1]   : Swap Number Scheme
    //  cmd_0 [0]   : RLE Compression
    // 
    CMD_L_MSK_SET_FLAGS       = 8'b1000_0010,

    // Sets the advanced trigger config.
    //
    // cmd = trg_sel | 24'h??????
    //
    // !!! TODO !!!
    // 
    CMD_OLS_ADV_TRG_CONG      = 8'b1001_1110,

    // Sets the advanced trigger data.
    // 
    // cmd = LSB .... MSB
    //
    // !!! TODO !!!
    //
    CMD_OLS_ADV_TRG_DATA      = 8'b1001_1111,

    // Sets the SUMP "basic" trigger mask. 
    // Each bit set to 1 will be considered by the trigger stage. 
    // In parallel mode, one bit corresponds to one channel, 
    // and in serial mode, each bit corresponds to one time-unit
    // for the selected channel.
    //
    // cmd = LSB ... MSB
    //
    CMD_L_MSK_SET_TRG_MSK     = 8'b1100_??00,

    // Sets the SUMP "basic" trigger values.
    // In parallel mode, one bit corresponds to one channel,
    // and in serial mode, each bit corresponds to one time-unit
    // for the selected channel.
    //
    // cmd = LSB ... MSB
    //
    CMD_L_MSK_SET_TRG_VAL     = 8'b1100_??01,

    // Sets the SUMP "basic" trigger configuration.
    // Configs marked with "x" are currently _not_ supported.
    // Configs marked with "~" will be supported in the next version.
    //
    // x    Stage Delay: If stage fires, the output is delayed by 
    //                   this number of samples.
    // ~    Serial Mode: 1=Serial, the trigger values are temporally compared.
    //                   In parallel mode, each bit is compared with the latest sample
    //                   of this channel. E.g., val[0] is compared with channel 0
    // ~    Serial Channel: The channel number selected for the serial trigger.
    // x    Level: Trigger level when current stage becomes active. 0=immediately.
    //      Start: Tell the controller that the basic trigger has fired.
    //
    // cmd = LSB | MSB | cmd_1 | cmd_0
    //       \-------/    
    //       stage delay
    //
    // cmd_1[7:4] : Serial Channel [3:0]
    // cmd_1[3:2] : dont cares
    // cmd_1[1:0] : Level
    // cmd_0[7:4] : dont care
    // cmd_0[3]   : Start
    // cmd_0[2]   : Serial Mode
    // cmd_0[1]   : dont care
    // cmd_0[0]   : Serial Channel [4]
    //
    CMD_L_MSK_SET_TRG_CONF    = 8'b1100_??10 } opcode_t;

  typedef enum logic {XON, XOFF} xcrtl_t;

endpackage


