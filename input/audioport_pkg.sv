`include "audioport.svh"

package audioport_pkg;

   //////////////////////////////////////////////////////////////////
   //
   // 1. Project parameters
   //
   //////////////////////////////////////////////////////////////////

`ifndef SYNTHESIS
   string mynumber                     = "2207831";   // At least 6 last digits of your student number
   localparam real CLK_PERIOD          = 18.5;        // Clock period
   localparam real MCLK_PERIOD         = 54.25347222; // Same for all students
`endif
   localparam int FILTER_TAPS          = 47;
   localparam int AUDIO_BUFFER_SIZE    = 32;
   localparam int CMD_WAIT_STATES      = 24; // Set manually to 6 + int'($ceil(6.0*MCLK_PERIOD/CLK_PERIOD) 

   //////////////////////////////////////////////////////////////////
   //
   // 2. Register counts for address computation
   //
   //////////////////////////////////////////////////////////////////

   // Number of coefficient registers for four FIR filters
   localparam int DSP_REGISTERS        = 188;

   // Number of 24-bit registers in abuf bank (ABUF0 and ABUF1, both AUDIO_BUFFER_SIZE * 2)
   localparam int ABUF_REGISTERS       = 128;
   

   // Total number of registers
   localparam int AUDIOPORT_REGISTERS  = 320;

   //////////////////////////////////////////////////////////////////
   //
   // 3. Register indices (rindex)
   //
   //////////////////////////////////////////////////////////////////

   localparam int CMD_REG_INDEX        = 0;
   localparam int STATUS_REG_INDEX     = 1;
   localparam int LEVEL_REG_INDEX      = 2;
   localparam int CFG_REG_INDEX        = 3;
   localparam int DSP_REGS_START_INDEX = 4;
   localparam int DSP_REGS_END_INDEX   = 191;
   localparam int ABUF0_START_INDEX    = 192;
   localparam int ABUF0_END_INDEX      = 255;
   localparam int ABUF1_START_INDEX    = 256;
   localparam int ABUF1_END_INDEX      = 319;

   localparam int RINDEX_BITS          = 9;// Number of bits in index values
   
   //////////////////////////////////////////////////////////////////
   //
   // 4. Register addresses in APB address spaces
   //
   //////////////////////////////////////////////////////////////////   

   localparam logic [31:0]  AUDIOPORT_START_ADDRESS  = 32'h8c000000;   
   localparam logic [31:0]  AUDIOPORT_END_ADDRESS    = 32'h8c0004FC;   
   localparam logic [31:0]  CMD_REG_ADDRESS          = 32'h8c000000;   
   localparam logic [31:0]  STATUS_REG_ADDRESS       = 32'h8c000004;   
   localparam logic [31:0]  LEVEL_REG_ADDRESS        = 32'h8c000008;   
   localparam logic [31:0]  CFG_REG_ADDRESS          = 32'h8c00000C;   
   localparam logic [31:0]  DSP_REGS_START_ADDRESS   = 32'h8c000010;   
   localparam logic [31:0]  DSP_REGS_END_ADDRESS     = 32'h8c0002FC;   
   localparam logic [31:0]  ABUF0_START_ADDRESS      = 32'h8c000300;   
   localparam logic [31:0]  ABUF0_END_ADDRESS        = 32'h8c0003FC;   
   localparam logic [31:0]  ABUF1_START_ADDRESS      = 32'h8c000400;   
   localparam logic [31:0]  ABUF1_END_ADDRESS        = 32'h8c0004FC;   
   
   //////////////////////////////////////////////////////////////////
   //
   // 5. Useful Constants
   //
   //////////////////////////////////////////////////////////////////   

   //----------------------------------------------------------------
   // a: Command register CMD_REG
   //----------------------------------------------------------------
   
   // Command codes (one-hot encoded)    
   localparam logic [31:0]  CMD_NOP =          32'h00000000;
   localparam logic [31:0]  CMD_CLR =          32'h00000001;
   localparam logic [31:0]  CMD_CFG =          32'h00000002;
   localparam logic [31:0]  CMD_START =        32'h00000004;
   localparam logic [31:0]  CMD_STOP =         32'h00000008;
   localparam logic [31:0]  CMD_LEVEL =        32'h00000010;   
   localparam logic [31:0]  CMD_IRQACK =       32'h00000020;

   //----------------------------------------------------------------
   // b: Status register STATUS_REG
   //----------------------------------------------------------------

   // Status bit indices
   localparam int 	   STATUS_PLAY      = 0;
   localparam int 	   STATUS_CLR_ERR   = 1;
   localparam int 	   STATUS_CFG_ERR   = 2;
   localparam int 	   STATUS_IRQ_ERR   = 3;
   localparam int 	   STATUS_CMD_ERR   = 4;   
   
   //----------------------------------------------------------------   
   // c: Configuration register CFG_REG   
   //----------------------------------------------------------------

   // Configuration bit indices
   localparam int 	    CFG_MONO = 2;
   localparam int 	    CFG_FILTER = 3;
   
   // Names of configuration bit values
   localparam logic [1:0]  RATE_48000  = 2'b00;
   localparam logic [1:0]  RATE_96000  = 2'b01;
   localparam logic [1:0]  RATE_192000 = 2'b10;
   localparam logic        FILTER_ON   = 1'b1;
   localparam logic        FILTER_OFF  = 1'b0;
   localparam logic        MONO_ON     = 1'b1;
   localparam logic        MODE_OFF    = 1'b0;   

   //----------------------------------------------------------------   
   // d: Clock divider rations (clk cycles per sample)
   //----------------------------------------------------------------   

`ifndef SYNTHESIS   
   localparam logic [31:0] CLK_DIV_48000  = int'($ceil((1000000000.0/48000.0)/(CLK_PERIOD)));
   localparam logic [31:0] CLK_DIV_96000  = int'($ceil((1000000000.0/96000.0)/(CLK_PERIOD)));
   localparam logic [31:0] CLK_DIV_192000 = int'($ceil((1000000000.0/192000.0)/(CLK_PERIOD)));
`endif
   
   //----------------------------------------------------------------      
   // e: Clock divider ratios for I2S interface (same for all students)
   //----------------------------------------------------------------
   
   localparam logic [31:0]  MCLK_DIV_48000 =        8;
   localparam logic [31:0]  MCLK_DIV_96000 =        4;
   localparam logic [31:0]  MCLK_DIV_192000 =       2;

   //----------------------------------------------------------------   
   // f: cdc_unit verification settings
   //----------------------------------------------------------------   

`ifndef SYNTHESIS
   localparam int 	    CDC_DATASYNC_INTERVAL   = 6 + int'(6.0*$ceil(MCLK_PERIOD/CLK_PERIOD)); // in clk cycles
   localparam int 	    CDC_DATASYNC_LATENCY    = 6 + int'(3.0*$ceil(MCLK_PERIOD/CLK_PERIOD)); // in mclk cycles
   localparam int 	    CDC_BITSYNC_INTERVAL    = int'($ceil(MCLK_PERIOD/CLK_PERIOD)); // in clk cycles
   localparam int 	    CDC_BITSYNC_LATENCY     = 2;  // in mclk cycles 
   localparam int 	    CDC_PULSESYNC_INTERVAL  = 1;  // in mclk cycles
   localparam int 	    CDC_PULSESYNC_LATENCY    = 2+int'($ceil(MCLK_PERIOD/CLK_PERIOD)); // in clk cycles
`endif

   //----------------------------------------------------------------      
   // g: dsp_unit max latency
   //----------------------------------------------------------------   

   localparam int 	    DSP_UNIT_MAX_LATENCY = 100;

endpackage
   
