////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for audioport
//
//    Contents:
//    1. X-Checks
//    2. Blackbox (functional) assumptions and assertions
//    3. Whitebox assertions
//    4. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

`ifndef SYNTHESIS

import audioport_pkg::*;
import audioport_util_pkg::*;

module audioport_svamod
  
  (input logic clk,
   input logic 			      rst_n,
   input logic 			      mclk,
   input logic 			      PSEL,
   input logic 			      PENABLE,
   input logic 			      PWRITE,
   input logic [31:0] 		      PADDR,
   input logic [31:0] 		      PWDATA,
   input logic [31:0] 		      PRDATA,
   input logic 			      PREADY,
   input logic 			      PSLVERR,
   input logic 			      irq_out,
   input logic 			      ws_out,
   input logic 			      sck_out, 
   input logic 			      sdo_out,
   input logic 			      test_mode_in,
   input logic 			      scan_en_in
 `ifndef SYSTEMC_DUT
,
   input logic 			      tick,
   input logic 			      play,
   input logic 			      cfg,
   input logic 			      level,
   input logic 			      clr,
   input logic [23:0] 		      audio0,
   input logic [23:0] 		      audio1,
   input logic [31:0] 		      cfg_reg,
   input logic [31:0] 		      level_reg,
   input logic [DSP_REGISTERS*32-1:0] dsp_regs,

   // dsp_unit

   input logic [23:0] 		      dsp0,
   input logic [23:0] 		      dsp1,
   input logic 			      dsp_tick,

   // cdc_unit   

   input logic 			      mclk_mux,      
   input logic 			      mrst_n,
   input logic 			      mtick,
   input logic 			      mplay,
   input logic 			      mreq,
   input logic 			      mcfg, 
   input logic [31:0] 		      mcfg_reg,
   input logic [23:0] 		      mdsp0,
   input logic [23:0] 		      mdsp1, 
   
   // i2s_unit   

   input logic 			      req
`endif
   );

`define anything_
  
`ifdef anything_
   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
   `xcheck(PSEL);
   `xcheck(PENABLE);
   `xcheck(PWRITE);
   `xcheck(PADDR);
   `xcheck(PWDATA);
   `xcheck(PRDATA);
   `xcheck(PREADY);
   `xcheck(PSLVERR);
   `xcheck(irq_out);
   `xcheck(test_mode_in);   
   `xcheck(scan_en_in);   
`ifndef SYSTEMC_DUT
   `xcheckm(sck_out); // xcheckm use mrst_n, which is an internal signal
   `xcheckm(ws_out);
   `xcheckm(sdo_out);   
   `xcheck(tick);
   `xcheck(play);
   `xcheck(req);
   `xcheck(cfg);
   `xcheck(level);
   `xcheck(clr);
   `xcheck(audio0);
   `xcheck(audio1);   
   `xcheck(dsp0);
   `xcheck(dsp1);
   `xcheck(dsp_tick);
   `xcheck(cfg_reg);
   `xcheck(level_reg);
   `xcheck(dsp_regs);
   `xcheckm(mtick);
   `xcheckm(mplay);
   `xcheckm(mreq);
   `xcheckm(mcfg);   
   `xcheckm(mcfg_reg);
   `xcheckm(mdsp0);
   `xcheckm(mdsp1);
 `endif //  `ifndef SYSTEMC_DUT
   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
 `include "apb_assumes.svh"

   property f_config_rule;
      @(posedge clk) disable iff (rst_n == '0)
	(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START)) |=>
	   !(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_CFG)) until
	   (PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP));
   endproperty
      
   mf_config_rule: assume property(f_config_rule);

   property f_clear_rule;
      @(posedge clk) disable iff (rst_n == '0)
	(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START)) |=>
	   !(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_CLR)) until
	   (PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP));
   endproperty
      
   mf_clear_rule: assume property(f_clear_rule);
   
   sequence s_ws;
      @(posedge clk)
	$rose(ws_out) ##1 ($rose(ws_out) [-> AUDIO_BUFFER_SIZE]);
   endsequence   

   sequence s_irq;
      @(posedge clk)
	$rose(irq_out) [= 1];
   endsequence   
   
   property f_irq_out_rise;
      @(posedge clk) disable iff (rst_n == '0)
        (!(PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_STOP)) throughout ($rose(ws_out) ##1 ($rose(ws_out) [-> AUDIO_BUFFER_SIZE]))) 
	implies 
	(($rose(ws_out) ##1 ($rose(ws_out) [-> AUDIO_BUFFER_SIZE]) ) intersect ($rose(irq_out) [= 1]));
   endproperty
      
   af_irq_out_rise: assert property(f_irq_out_rise);
   cf_irq_out_rise: cover property(f_irq_out_rise);   


   property f_irq_out_fall;
      @(posedge clk) disable iff (rst_n == '0)
        irq_out && PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && ((PWDATA == CMD_STOP) || (PWDATA == CMD_IRQACK)) |=> !irq_out;
   endproperty
      
   af_irq_out_fall: assert property(f_irq_out_fall);
   cf_irq_out_fall: cover property(f_irq_out_fall);   


   property f_enter_play_mode;
      @(posedge clk) disable iff (rst_n == '0)
        PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START) |=>
					 1 [* 0:CLK_DIV_48000] ##1 sck_out;
   endproperty
      
   af_enter_play_mode: assert property(f_enter_play_mode);
   cf_enter_play_mode: cover property(f_enter_play_mode);   

   property f_enter_standby_mode;
      @(posedge clk) disable iff (rst_n == '0)
        PSEL && PWRITE && PENABLE && PREADY && (PADDR == CMD_REG_ADDRESS) && (PWDATA == CMD_START) |=>
					 1 [* 0:CLK_DIV_48000] ##1 !sck_out;
   endproperty
      
   af_enter_standby_mode: assert property(f_enter_standby_mode);
   cf_enter_standby_mode: cover property(f_enter_standby_mode);   



   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

 `ifndef SYSTEMC_DUT   
   property r_data_roundtrip;
      @(posedge mclk) disable iff (mrst_n == '0)
	(play throughout ($fell(ws_out) ##1 $fell(ws_out) [-> 1]))
	implies
					   ($fell(ws_out) ##1 $fell(ws_out) [-> 1]) intersect ($rose(mreq) [= 1] ##1 $rose(mtick) [= 1]);
   endproperty

   ar_data_roundtrip: assert property ( r_data_roundtrip )
     else $error("roundtripfailure.");
   cr_data_roundtrip: cover property ( r_data_roundtrip );
 `endif

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   
`ifndef SYSTEMC_DUT
   
   covergroup cg_active_config with function sample(logic [3:0] cfgbits);
      configs: coverpoint cfgbits
	{ 
         bins cfgmodes[]= { 4'b0000, 4'b0001, 4'b0010,
                            4'b0100, 4'b0101, 4'b0110,
                            4'b1000, 4'b1001, 4'b1010,
                            4'b1100, 4'b1101, 4'b1110 };
      }
   endgroup

   cg_active_config cg_active_config_inst = new;

   property f_active_config;
      @(posedge clk ) disable iff (rst_n == '0)
	cfg ##1 (!cfg throughout $rose(play) [-> 1]) |-> (1, cg_active_config_inst.sample(cfg_reg[3:0]));
   endproperty      
   
   cf_active_config: cover property(f_active_config);

`endif //  `ifndef SYSTEMC_DUT

`endif //  `ifdef anything_
   
endmodule

`endif
