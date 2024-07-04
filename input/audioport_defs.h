#ifndef audioport_defs_h
#define audioport_defs_h

// Design parameters

//////////////////////////////////////////////////////////////////
//
// 1. Project parameters
//
//////////////////////////////////////////////////////////////////

#define CLK_PERIOD          18.5
#define MCLK_PERIOD         54.25347222
#define FILTER_TAPS         47
#define AUDIO_BUFFER_SIZE   32
#define CMD_WAIT_STATES     24

//////////////////////////////////////////////////////////////////
//
// 2. Register counts for address computation
//
//////////////////////////////////////////////////////////////////

#define DSP_REGISTERS       1
#define ABUF_REGISTERS      1
#define AUDIOPORT_REGISTERS 1

//////////////////////////////////////////////////////////////////
//
// 3. Register indices (rindex)
//
//////////////////////////////////////////////////////////////////

#define RINDEX_BITS           0
#define CMD_REG_INDEX         0
#define STATUS_REG_INDEX      0
#define LEVEL_REG_INDEX       0
#define CFG_REG_INDEX         0
#define DSP_REGS_START_INDEX  0
#define DSP_REGS_END_INDEX    0
#define ABUF0_START_INDEX     0
#define ABUF0_END_INDEX       0
#define ABUF1_START_INDEX     0
#define ABUF1_END_INDEX       0
   
//////////////////////////////////////////////////////////////////
//
// 4. Register addresses in APB address spaces
//
//////////////////////////////////////////////////////////////////   

#define AUDIOPORT_START_ADDRESS  0x8c000000   
#define AUDIOPORT_END_ADDRESS    0x8c000000   
#define CMD_REG_ADDRESS          0x8c000000   
#define STATUS_REG_ADDRESS       0x8c000000   
#define LEVEL_REG_ADDRESS        0x8c000000   
#define CFG_REG_ADDRESS          0x8c000000   
#define DSP_REGS_START_ADDRESS   0x8c000000   
#define DSP_REGS_END_ADDRESS     0x8c000000   
#define ABUF_START_ADDRESS       0x8c000000   
#define ABUF_END_ADDRESS         0x8c000000   
#define ABUF0_START_ADDRESS      0x8c000000   
#define ABUF0_END_ADDRESS        0x8c000000   
#define ABUF1_START_ADDRESS      0x8c000000   
#define ABUF1_END_ADDRESS        0x8c000000   

//////////////////////////////////////////////////////////////////
//
// 5. Useful Constants
//
//////////////////////////////////////////////////////////////////   


// a: Command register CMD_REG

#define CMD_NOP          0x0
#define CMD_CLR          0x1
#define CMD_CFG          0x2
#define CMD_START        0x4
#define CMD_STOP         0x8
#define CMD_LEVEL        0x10   
#define CMD_IRQACK       0x20   

// b: Status register STATUS_REG

// Status bit indices
#define STATUS_PLAY      0
#define STATUS_CLR_ERR   1
#define STATUS_CFG_ERR   2
#define STATUS_IRQ_ERR   3
#define STATUS_CMD_ERR   4

// c: Configuration register CFG_REG   

// Configuration bit indices

#define CFG_MONO      2
#define CFG_FILTER    3

// Names of configuration bit values

#define FILTER_ON     1
#define FILTER_OFF    0
#define MONO_ON       1
#define MONO_OFF      0
#define RATE_48000    0
#define RATE_96000    1
#define RATE_192000   2

// d: Constants used in dsp_unit

#define DATABITS      24
#define COEFFBITS     32
#define ACCBITS       2
#define SUMBITS       2

// e: These are needed in the testbench

#define CLK_DIV_48000        ((1000000000.0/48000.0)/(CLK_PERIOD))
#define CLK_DIV_96000        ((1000000000.0/96000.0)/(CLK_PERIOD))
#define CLK_DIV_192000       ((1000000000.0/192000.0)/(CLK_PERIOD))

#endif
