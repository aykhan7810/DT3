////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for control_unit
//
//    Contents:
//    1. X-Checks
//    2. Assumptions for formal verification
//    3. Blackbox assertions
//    4. Whitebox assertions
//    5. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module i2s_unit_svamod
  (
   input logic 	      clk,
   input logic 	      rst_n,
   input logic 	      play_in,
   input logic [23:0] audio0_in,
   input logic [23:0] audio1_in,
   input logic 	      tick_in,
   input logic 	      req_out,
   input logic 	      cfg_in,
   input logic [31:0] cfg_reg_in,
   input logic 	      sck_out,
   input logic 	      ws_out,
   input logic 	      sdo_out
`ifndef SYSTEMC_DUT
	input logic	[1:0] cfg_r;
	input logic play_r;
	input logic req_r;
	input logic [47:0] audio_r;
	input logic [47:0] shift_r;

`endif   
   );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   `xcheck(play_in);
   `xcheck(audio0_in);
   `xcheck(audio1_in);
   `xcheck(tick_in);
   `xcheck(req_out);
   `xcheck(cfg_in);
   `xcheck(cfg_reg_in);
   `xcheck(sck_out);
   `xcheck(ws_out);
   `xcheck(sdo_out);
`ifndef SYSTEMC_DUT

`endif   


   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

 `ifdef design_top_is_i2s_unit // Assumptions enabled only in i2s_unit verification

   // play_in_length : f_play_in_stable

   property f_play_in_stable;
    @(posedge clk ) disable iff (rst_n == '0)
      !$stable(play_in) |=> $stable(play_in) [* 384];
 endproperty
   
   mf_play_in_stable: assume property(f_play_in_stable) else assert_error("mf_play_in_stable");
   cf_play_in_stable: cover property(f_play_in_stable);

   // cfg_in_length : f_cfg_in_pulse

   property f_cfg_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(cfg_in) |=> $fell(cfg_in);
   endproperty

   mf_cfg_in_pulse: assume property(f_cfg_in_pulse) else assert_error("mf_cfg_in_pulse");
   cf_cfg_in_pulse: cover property(f_cfg_in_pulse);

   // tick_in_length : f_tick_in_pulse

   property f_tick_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(tick_in) |=> $fell(tick_in);
   endproperty

   mf_tick_in_pulse: assume property(f_tick_in_pulse) else assert_error("mf_tick_in_pulse");
   cf_tick_in_pulse: cover property(f_tick_in_pulse);

   // tick_in_length : f_tick_in_play_only

   property f_tick_in_play_only;
      @(posedge clk ) disable iff (rst_n == '0)
	!play_in |-> !tick_in;
   endproperty

   mf_tick_in_play_only: assume property(f_tick_in_play_only) else assert_error("mf_tick_in_play_only");
   cf_tick_in_play_only: cover property(f_tick_in_play_only);

 `endif //  `ifdef design_top_is_i2s_unit
   
   // data_request : f_req_out_pulse

   property f_req_out_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(req_out) |=> $fell(req_out);
   endproperty

   af_req_out_pulse: assert property(f_req_out_pulse) else assert_error("af_req_out_pulse");
   cf_req_out_pulse: cover property(f_req_out_pulse);

   // data_request : f_req_sck_align

   property f_req_sck_align;
      @(posedge clk ) disable iff (rst_n == '0)
	$fell(req_out) |-> $fell(sck_out);
   endproperty

   af_req_sck_align: assert property(f_req_sck_align) else assert_error("af_req_sck_align");
   cf_req_sck_align: cover property(f_req_sck_align);

   // data_request : f_req_out_seen

   property f_req_out_seen;
      @(posedge clk ) disable iff (rst_n == '0)
	($rose(play_in) || (play_in && $fell(ws_out))) ##1 play_in throughout ($fell(sck_out) [-> 1]) |-> $past(req_out);
   endproperty

   af_req_out_seen: assert property(f_req_out_seen) else assert_error("af_req_out_seen");
   cf_req_out_seen: cover property(f_req_out_seen);

   // sck_wave : f_sck_wave

   property f_sck_wave;
      @(posedge clk ) disable iff (rst_n == '0)
	$rose(sck_out) |=> (sck_out [*3] ##1 !sck_out[*4]) or
					  (sck_out [*1] ##1 !sck_out[*2]) or 
					  $fell(sck_out);
   endproperty

   af_sck_wave: assert property(f_sck_wave) else assert_error("af_sck_wave");
   cf_sck_wave: cover property(f_sck_wave);

   // ws_wave : f_ws_change

   property f_ws_change;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(ws_out) |-> $fell(sck_out);
   endproperty

   af_ws_change: assert property(f_ws_change) else assert_error("af_ws_change");
   cf_ws_change: cover property(f_ws_change);

   // ws_wave : f_ws_wave

   property f_ws_wave;
      @(posedge clk ) disable iff (rst_n == '0)
	!ws_out throughout $rose(sck_out) [-> 24] |=> $rose(ws_out) [-> 1] ##1 ws_out throughout $rose(sck_out) [-> 24] ;
   endproperty

   af_ws_wave: assert property(f_ws_wave) else assert_error("af_ws_wave");
   cf_ws_wave: cover property(f_ws_wave);

   // serial_data : f_sdo_change

   property f_sdo_change;
      @(posedge clk ) disable iff (rst_n == '0)
	!$stable(sdo_out) && play_in |-> $fell(sck_out);
   endproperty

   af_sdo_change: assert property(f_sdo_change) else assert_error("af_sdo_change");
   cf_sdo_change: cover property(f_sdo_change);

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifndef SYSTEMC_DUT

	// cfg_r_stable : ar_cfg_r_stable

	property r_cfg_r_stability;
    	@(posedge clk) disable iff (rst_n == '0)
    (play_r | !cfg_in) |-> $stable(cfg_r);
	endproperty

	ar_cfg_r_stable: assert property(r_cfg_r_stable) else assert_error("ar_cfg_r_stable");
	cr_cfg_r_stable: cover property(r_cfg_r_stable);

   
    // mode_control : ar_output_standby_mode

	property r_output_standby_mode;
    	@(posedge clk) disable iff (rst_n == '0)
   	(!play_in) |-> (sck_out == '0 && ws_out == '0 && sdo_out == '0);
   	endproperty

	ar_output_standby_mode: assert property(r_output_standby_mode) else assert_error("ar_output_standby_mode");
	cr_output_standby_mode: cover property(r_output_standby_mode);
	
	// config_interface : ar_cfg_r_update
	
	property r_cfg_r_update;
    	@(posedge clk) disable iff (rst_n == '0)
   	(!play_in && cfg_in) |-> (cfg_r == cfg_reg_in[1:0]);
   	endproperty

	ar_cfg_r_update: assert property(r_cfg_r_update) else assert_error("ar_cfg_r_update");
	cr_cfg_r_update: cover property(r_cfg_r_update);
	
	// audio_interface : ar_audio_reg_behavior
	
	property r_audio_reg_behavior;
    	@(posedge clk) disable iff (rst_n == '0)
   	(play_in && tick_in) |-> (audio_r == {audio0_in, audio1_in});
   	endproperty

	ar_audio_reg_behavior: assert property(r_audio_reg_behavior) else assert_error("ar_audio_reg_behavior");
	cr_audio_reg_behavior: cover property(r_audio_reg_behavior);
	
	// audio_interface : ar_audio_reg_standby
	
	property r_audio_reg_standby;
    	@(posedge clk) disable iff (rst_n == '0)
   	(!play_in) |-> (!audio_r);
   	endproperty

	ar_audio_reg_standby: assert property(r_audio_reg_standby) else assert_error("ar_audio_reg_standby");
	cr_audio_reg_standby: cover property(r_audio_reg_standby);
	
	// data_request : ar_req_out_timing
	
	property r_req_out_timing;
    	@(posedge clk) disable iff (rst_n == '0)
   	(!sck_out) |-> (req_out);
   	endproperty

	ar_req_out_timing: assert property(r_req_out_timing) else assert_error("ar_req_out_timing");
	cr_req_out_timing: cover property(r_req_out_timing);
	
	
	// shift_register : ar_shift_reg_load
	
	property r_shift_reg_load;
    	@(posedge clk) disable iff (rst_n == '0)
   	(req_out && play_in) |-> (shift_r == audio_r);
   	endproperty

	ar_shift_reg_load: assert property(r_shift_reg_load) else assert_error("ar_shift_reg_load");
	cr_shift_reg_load: cover property(r_shift_reg_load);
	
	// shift_register : ar_shift_reg_shift
	
	property r_shift_reg_shift;
    	@(posedge clk & negedge sck_out) disable iff (rst_n == '0)
    (!req_out) |-> (shift_r[46:0] == $past(shift_r[47:1]));
   	endproperty

	ar_shift_reg_shift: assert property(r_shift_reg_shift) else assert_error("ar_shift_reg_shift");
	cr_shift_reg_shift: cover property(r_shift_reg_shift);
	
	// shift_register : ar_shift_reg_zero

	property r_shift_reg_zero;
    	@(posedge clk) disable iff (rst_n == '0)
    (play_in) |-> (!shift_r && !audio_r);
	endproperty

	ar_shift_reg_zero : assert property(r_shift_reg_zero) else $error("ar_shift_reg_zero");
	cr_shift_reg_zero: cover property(r_shift_reg_zero);

`endif
   

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifndef SYSTEMC_DUT

`endif


endmodule




