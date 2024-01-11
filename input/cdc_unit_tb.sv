`ifndef SYNTHESIS

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module cdc_unit_tb   #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk = '0;
   logic rst_n;
   logic test_mode_in;
   logic [23:0] dsp0_in;
   logic [23:0] dsp1_in;   
   logic 	play_in;
   logic 	tick_in;
   logic 	cfg_in;
   logic [31:0] cfg_reg_in;
   logic 	req_out;
   
   logic 	mclk_in ='0;
   logic 	mclk;
   logic 	mrst_n;
   logic [23:0] dsp0_out;
   logic [23:0] dsp1_out;   
   logic 	play_out;
   logic 	tick_out;
   logic 	cfg_out;
   logic [31:0] cfg_reg_out;
   logic 	req_in;
   
   logic 	     ref_mclk;
   logic 	     ref_mrst_n;
   logic [23:0]      ref_dsp0_out;
   logic [23:0]      ref_dsp1_out;
   logic 	     ref_play_out;
   logic 	     ref_tick_out;
   logic 	     ref_cfg_out;
   logic [31:0]      ref_cfg_reg_out;
   logic 	     ref_req_out;

   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Clock, reset generation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   initial
     begin
	realtime delay;
	int counter;
	counter = 0;
	clk = '0;
	forever
	  begin 
	     #(CLK_PERIOD/2) clk = ~clk;
	     ++counter;
	     if (counter == 101)
	       begin
		  // Insert random delay to make clk and mclk start out of synch		  
		  delay = real'($urandom_range(0, CLK_PERIOD/2))/23.0;
		  #(delay);
		  counter = 0;
	       end
	  end
     end
   
   initial
     begin
	realtime delay;
	mclk_in = '0;
	// Insert random delay to make clk and mclk start out of synch
	delay = real'($urandom_range(0, MCLK_PERIOD/2))/11.0;
	#(delay);
	forever begin
	   #(MCLK_PERIOD/2) mclk_in = ~mclk_in;
	end
     end
   
   ////////////////////////////////////////////////////////////////////////////
   //
   // Instantiation of DUT and test program
   //
   ////////////////////////////////////////////////////////////////////////////

   cdc_unit DUT_INSTANCE (
			  .clk(clk),
			  .rst_n(rst_n),
			  .test_mode_in(test_mode_in),
			  .dsp0_in(dsp0_in),
			  .dsp1_in(dsp1_in),
			  .play_in(play_in),
			  .tick_in(tick_in),
			  .cfg_in(cfg_in),
			  .cfg_reg_in(cfg_reg_in),
			  .req_out(req_out),
			  .mclk_in(mclk_in),
			  .mclk(mclk),
			  .mrst_n(mrst_n),
			  .dsp0_out(dsp0_out),
			  .dsp1_out(dsp1_out), 
			  .play_out(play_out),
			  .tick_out(tick_out),
			  .cfg_out(cfg_out),
			  .cfg_reg_out(cfg_reg_out),
			  .req_in(req_in)
			  );
   
   cdc_unit_test TEST (.*);

   ////////////////////////////////////////////////////////////////////////////
   //
   // Include SVA assertion module bindings only in RTL simulation
   //
   ////////////////////////////////////////////////////////////////////////////

`include "sva_bindings.svh"

   ////////////////////////////////////////////////////////////////////////////
   //
   // Reference model instantiation
   //
   ////////////////////////////////////////////////////////////////////////////
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL

	    cdc_unit REF_INSTANCE
	      (.clk(clk),
	       .rst_n(rst_n),
	       .test_mode_in(test_mode_in),
	       .mclk_in(mclk_in),
	       .mclk(ref_mclk),
	       .mrst_n(ref_mrst_n),
	       .dsp0_out(ref_dsp0_out),
	       .dsp1_out(ref_dsp1_out),	       
	       .cfg_out(ref_cfg_out),
	       .play_out(ref_play_out),
	       .tick_out(ref_tick_out),
	       .cfg_reg_out(ref_cfg_reg_out),
	       .req_out(ref_req_out),
	       .*
	       );

      end 

      
   endgenerate

   initial
     begin
	save_test_parameters("reports/3_vsim_cdc_unit_test_parameters.txt");	
     end
   
endmodule // cdc_unit_tb


`endif
