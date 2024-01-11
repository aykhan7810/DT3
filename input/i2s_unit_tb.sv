`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module i2s_unit_tb;
   logic 	   clk;
   logic 	   rst_n;
   logic 	   play_in;
   logic 	   tick_in;   
   logic [23:0]    audio0_in;
   logic [23:0]    audio1_in;   
   logic 	   cfg_in;
   logic [31:0]    cfg_reg_in;
   logic 	   req_out;
   logic  ws_out;
   logic  sck_out;
   logic  sdo_out;

   i2s_if i2s(rst_n);
   assign i2s.sdo = sdo_out;
   assign i2s.sck = sck_out;
   assign i2s.ws  = ws_out;
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	clk = '0;
	forever #(MCLK_PERIOD/2) clk = ~clk;
     end
   
   initial
     begin
	rst_n = '0;
	@(negedge clk) rst_n = '0;
	@(negedge clk) rst_n = '1;	
     end

   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////
   
   i2s_unit DUT_INSTANCE (
			  .clk(clk),
			  .rst_n(rst_n),
			  .play_in(play_in),
			  .tick_in(tick_in),
			  .audio0_in(audio0_in),
			  .audio1_in(audio1_in),
			  .cfg_in(cfg_in),
			  .cfg_reg_in(cfg_reg_in),
			  .req_out(req_out),
			  .ws_out(ws_out),
			  .sck_out(sck_out),
			  .sdo_out(sdo_out)
			  );

   i2s_unit_test TEST    (
			  .clk(clk),
			  .rst_n(rst_n),
			  .play_in(play_in),
			  .tick_in(tick_in),
			  .audio0_in(audio0_in),
			  .audio1_in(audio1_in),
			  .cfg_in(cfg_in),
			  .cfg_reg_in(cfg_reg_in),
			  .req_out(req_out),
			  .ws_out(ws_out),
			  .sck_out(sck_out),
			  .sdo_out(sdo_out),
			  .i2s(i2s)
			  );

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings
   //
   ////////////////////////////////////////////////////////////////////////////

`include "sva_bindings.svh"

   initial
     begin
	save_test_parameters("reports/3_vsim_i2s_unit_test_parameters.txt");	
     end
   
endmodule 


`endif
