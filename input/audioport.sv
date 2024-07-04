//
//  audioport.sv: Top-level module of audioport design.
//

`include "audioport.svh"

import audioport_pkg::*;

module audioport
  
  (input logic clk,
   input logic rst_n,
   input logic mclk,

   // APB interface
   
   input logic  PSEL,
   input logic  PENABLE,
   input logic  PWRITE,
   input logic [31:0]  PADDR,
   input logic [31:0] PWDATA,
   output logic [31:0] PRDATA,
   output logic PREADY,
   output logic PSLVERR,

   // Interrupt request
   //    
   output logic irq_out,
   
   // Audio outputs

   output logic ws_out,
   output logic sck_out,   
   output logic sdo_out,

   // Test signals
   input logic 	       test_mode_in,
   input logic 	       scan_en_in

   );


   /////////////////////////////////////////////////////////////////////////////
   //
   // Internal signal variables
   //
   /////////////////////////////////////////////////////////////////////////////

   // control_unit outputs
   logic [31:0]        cfg_reg;
   logic [DSP_REGISTERS*32-1:0] dsp_regs;
   logic [31:0] 		level_reg;
   logic [23:0] 		audio0;
   logic [23:0] 		audio1;
   logic 			clr;
   logic 			level;
   logic 			cfg;
   logic 			tick;
   logic 			play;
  
   // dsp_unit outputs
   logic [23:0] 		dsp0;
   logic [23:0] 		dsp1;
   logic 			dsp_tick;

   // cdc_unit outputs
   logic [31:0] 		mcfg_reg;
   logic [23:0] 		mdsp0;
   logic [23:0] 		mdsp1;
   logic 			mtick;
   logic 			mcfg;
   logic 			mplay;
   logic 			mclk_mux;
   logic 			mrst_n;
   logic 			req;

   // i2s_unit outputs
   logic 			mreq;

   /////////////////////////////////////////////////////////////////////////////
   //
   // control_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   control_unit control_unit_1
     (
      .clk(clk),
      .rst_n(rst_n),
      .PREADY(PREADY),
      .PSEL(PSEL),
      .PENABLE(PENABLE),
      .PWRITE(PWRITE),
      .PADDR(PADDR),
      .PWDATA(PWDATA),
      .PRDATA(PRDATA),
      .PSLVERR(PSLVERR),
      .irq_out(irq_out),
      .cfg_reg_out(cfg_reg),
      .dsp_regs_out(dsp_regs),
      .level_reg_out(level_reg),
      .audio0_out(audio0),
      .audio1_out(audio1),
      .clr_out(clr),
      .level_out(level),
      .cfg_out(cfg),
      .tick_out(tick),
      .play_out(play),
      .req_in(req)
      );

   /////////////////////////////////////////////////////////////////////////////
   //
   // dsp_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
 dsp_unit dsp_unit_1
   (
    .clk(clk),
    .rst_n(rst_n),
    .cfg_reg_in(cfg_reg),
    .dsp_regs_in(dsp_regs),
    .level_reg_in(level_reg),
    .audio0_in(audio0),
    .audio1_in(audio1),
    .clr_in(clr),
    .level_in(level),
    .cfg_in(cfg),
    .tick_in(tick),
    .dsp0_out(dsp0),
    .dsp1_out(dsp1),
    .valid_out(dsp_tick)	     
    );

   /////////////////////////////////////////////////////////////////////////////
   //
   // cdc_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   cdc_unit cdc_unit_1 
     (
      .clk(clk),
      .rst_n(rst_n),
      .test_mode_in(test_mode_in),
      .mclk_in(mclk),
      .cfg_reg_in(cfg_reg),
      .dsp0_in(dsp0),
      .dsp1_in(dsp1),
      .tick_in(dsp_tick),
      .cfg_in(cfg),
      .play_in(play),
      .req_out(req),
      .cfg_reg_out(mcfg_reg),
      .dsp0_out(mdsp0),
      .dsp1_out(mdsp1),
      .tick_out(mtick),
      .cfg_out(mcfg),
      .play_out(mplay),
      .req_in(mreq),
      .mclk(mclk_mux),
      .mrst_n(mrst_n)
      );

   /////////////////////////////////////////////////////////////////////////////
   //
   // i2s_unit instantiation
   //
   /////////////////////////////////////////////////////////////////////////////
   
   i2s_unit i2s_unit_1
     (
      .clk(mclk_mux),
      .rst_n(mrst_n),
      .cfg_reg_in(mcfg_reg),
      .audio0_in(mdsp0),
      .audio1_in(mdsp1),
      .tick_in(mtick),
      .cfg_in(mcfg),
      .play_in(mplay),
      .req_out(mreq),
      .ws_out(ws_out),
      .sck_out(sck_out),
      .sdo_out(sdo_out)
      );

endmodule


