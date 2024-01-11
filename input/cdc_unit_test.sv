//
//  cdc_unit.sv: test program for cdc_unit.
//

// `define FORCE_PROTOCOL_FAILURE 1

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program cdc_unit_test(
		input logic 	    clk,
		output logic 	    rst_n,
		output logic 	    test_mode_in,
		output logic [23:0] dsp0_in,
		output logic [23:0] dsp1_in, 
		output logic 	    play_in,
		output logic 	    tick_in, 
		output logic 	    cfg_in,
		output logic [31:0] cfg_reg_in,
		input logic 	    req_out,
		      
		input logic 	    mclk_in,
		input logic 	    mclk, 
		input logic 	    mrst_n,
		input logic [23:0]  dsp0_out,
		input logic [23:0]  dsp1_out, 
		input logic 	    play_out,
		input logic 	    tick_out,
		input logic 	    cfg_out,
		input logic [31:0]  cfg_reg_out,
		output logic 	    req_in
		);

   real  tmaxlatency;
   real  reset_sync_latency;
   real  play_sync_latency;
   real  req_sync_latency;
   real  cfg_sync_latency;
   real  audio_sync_latency;
   logic timer_clk;
   
   clocking cb_clk @(posedge clk);
      input 			    req_out;
      output 			    #(CLK_PERIOD/8.0) play_in, tick_in, dsp0_in, dsp1_in, cfg_in, cfg_reg_in;
   endclocking

   clocking cb_mclk @(posedge mclk);
      input 			    play_out, tick_out, dsp0_out, dsp1_out, cfg_out, cfg_reg_out;
      output 			    #(MCLK_PERIOD/8.0) req_in;
   endclocking
   
`include "cdc_unit_test_tasks.svh"
   
   initial
     begin
	fork
	   begin

	      // Disable assertions for synchonized outputs and enable them later
	      // if the respective synchronizer module is detected
`ifndef SYSTEMC_DUT	      
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_reset_sync_01);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_reset_sync_10);   
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_reset_sync_01);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_reset_sync_10);   

	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_play_sync);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_play_sync);   
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_play_out);   

	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_req_sync);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_req_sync); 
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_req_out_pulse);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_req_out_pulse);     
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_req_out);   
	      
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_cfg_sync);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_cfg_sync); 
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_cfg_out);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_cfg_reg_out);      

	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_audio_sync);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_audio_sync); 
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_tick_out);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_dsp0_out);
	      $assertoff(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_dsp1_out);         
`endif
	      // Initialize test statistics
	      tmaxlatency = 0.0;
	      reset_test_stats;
	      
	      // Initialize input ports
	      
	      rst_n = '0;
	      test_mode_in = '0;
	      play_in = '0;
	      tick_in = '0;
	      cfg_in = '0;
	      cfg_reg_in = '0;
	      dsp0_in = '0;
	      dsp1_in = '0;	
	      req_in = '0;
	      @(negedge clk);
	      
	      // Run tasks

	      if (!$isunknown(mclk) && !$isunknown(mrst_n)) 
		begin
		   testmux_test;
		end
	      else
		$warning("testmux_test not executed because of uknown module outputs");

	      if (!$isunknown(mrst_n))
		begin
`ifndef SYSTEMC_DUT	      
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_reset_sync_01);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_reset_sync_10);   
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_reset_sync_01);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_reset_sync_10);   
`endif
		   reset_sync_test;
		end
	      else
		$warning("reset_sync_test not executed because of uknown module outputs");	      

	      if (!$isunknown(play_out))	      
		begin
`ifndef SYSTEMC_DUT	      
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_play_sync);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_play_sync);   
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_play_out);   
`endif
		   play_sync_test;
		end
	      else
		$warning("play_sync_test not executed because of uknown module outputs");	      

	      if (!$isunknown(req_out))	      	      
		begin
`ifndef SYSTEMC_DUT	      
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_req_sync);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_req_sync); 
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_req_out_pulse);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_req_out_pulse);     
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_req_out);   
`endif
		   pulse_sync_test;
		end
	      else
		$warning("pulse_sync_test not executed because of uknown module outputs");	      

	      if (!$isunknown(cfg_out) && !$isunknown(cfg_reg_out))
		begin
`ifndef SYSTEMC_DUT	      
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_cfg_sync);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_cfg_sync); 
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_cfg_out);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_cfg_reg_out);      
`endif
		   cfg_sync_test;
		end
	      else
		$warning("cfg_sync_test not executed because of uknown module outputs");	      

	      if (!$isunknown(tick_out) && !$isunknown(dsp0_out) && !$isunknown(dsp1_out))
		begin
`ifndef SYSTEMC_DUT	      
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.af_audio_sync);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.cf_audio_sync); 
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_tick_out);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_dsp0_out);
		   $asserton(0, $root.cdc_unit_tb.DUT_INSTANCE.CHECKER_MODULE.X_dsp1_out);         
`endif
		   audio_sync_test;
		end
	      else
		$warning("audio_sync_test not executed because of uknown module outputs");	      

	      $display("#####################################################################################################");	
	      $display("cdc_unit_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
	      $display("#####################################################################################################");	
	      $display(" ");
	      $display("------------------------------------");
	      $display("Crossing   |        Latency ");
	      $display("           |        ns  clk mclk");	      
	      $display("------------------------------------");
	      $display("reset_sync |  %8.3f %4d %4d", reset_sync_latency,   $ceil(reset_sync_latency/CLK_PERIOD),  $ceil(reset_sync_latency/MCLK_PERIOD) );   
	      $display("play_sync  |  %8.3f %4d %4d", play_sync_latency,   $ceil(play_sync_latency/CLK_PERIOD),  $ceil(play_sync_latency/MCLK_PERIOD) );
	      $display("req_sync   |  %8.3f %4d %4d", req_sync_latency,    $ceil(req_sync_latency/CLK_PERIOD),   $ceil(req_sync_latency/MCLK_PERIOD)  );
	      $display("cfg_sync   |  %8.3f %4d %4d", cfg_sync_latency,    $ceil(cfg_sync_latency/CLK_PERIOD),   $ceil(cfg_sync_latency/MCLK_PERIOD)  );
	      $display("audio_sync |  %8.3f %4d %4d", audio_sync_latency,  $ceil(audio_sync_latency/CLK_PERIOD), $ceil(audio_sync_latency/MCLK_PERIOD));			
	      $display("-----------------------------------");	
	      
	      $finish;
	   end

	   begin
	      timer_clk = '0;
	      forever
		#(CLK_PERIOD/8) timer_clk = ~timer_clk;
	   end
	   
	   begin
	      #(WATCHDOG_TIME);
	      $error("WATCHDOG_TIME exceeded!");
	      $finish;
	   end
	join_any
     end

   
   
endprogram
