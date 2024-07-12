////////////////////////////////////////////////////////////////////////////////////////////
//
// SystemVerilog assertion module file for control_unit
//
//    Contents:
//    1. X-Checks
//    2. Blackbox (functional) assumptions and assertions
//    3. Whitebox assertions
//    4. Covergroups
//
////////////////////////////////////////////////////////////////////////////////////////////

`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

module control_unit_svamod
  (
   input logic 					 clk,
   input logic 					 rst_n,
   input logic 					 PSEL,
   input logic 					 PENABLE,
   input logic 					 PWRITE,
   input logic [31:0] 				 PADDR,
   input logic [31:0] 				 PWDATA,
   input logic 					 req_in,
   input logic [31:0] 				 PRDATA,
   input logic 					 PSLVERR,
   input logic 					 PREADY,
   input logic 					 irq_out,
   input logic [31:0] 				 cfg_reg_out,
   input logic [31:0] 				 level_reg_out,
   input logic [DSP_REGISTERS*32-1:0] 		 dsp_regs_out,
   input logic 					 cfg_out,
   input logic 					 clr_out,
   input logic 					 level_out,
   input logic 					 tick_out,
   input logic [23:0] 				 audio0_out,
   input logic [23:0] 				 audio1_out,
   input logic 					 play_out
`ifndef SYSTEMC_DUT
   ,
   input logic [$clog2(AUDIOPORT_REGISTERS)-1:0] rindex,
   input logic [$clog2(CMD_WAIT_STATES):0] 	 wctr_r,
   input logic [AUDIOPORT_REGISTERS-1:0][31:0] 	 rbank_r,
   input logic 					 cmd_exe,
   input logic 					 cmd_err,
   input logic 					 start,
   input logic 					 stop,
   input logic 					 irqack,
   input logic 					 play_r,
   input logic 					 clr,
   input logic 					 clr_err,
   input logic 					 cfg_err,
   input logic 					 req_r,
   input logic [$clog2(ABUF_REGISTERS)-1:0] 	 rctr_r,
   input logic 					 irq_r,
   input logic 					 irq_err
`endif
   );

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 1. X-checks
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

   `xcheck(PSEL);
   `xcheck(PENABLE);
   `xcheck(PWRITE);
   `xcheck(PADDR);
   `xcheck(PWDATA);
   `xcheck(req_in);
   `xcheck(PRDATA);
   `xcheck(PSLVERR);
   `xcheck(PREADY);
   `xcheck(irq_out);
   `xcheck(cfg_reg_out);
   `xcheck(level_reg_out);
   `xcheck(dsp_regs_out);
   `xcheck(cfg_out);
   `xcheck(clr_out);
   `xcheck(level_out);
   `xcheck(tick_out);
   `xcheck(audio0_out);
   `xcheck(audio1_out);
   `xcheck(play_out);
`ifndef SYSTEMC_DUT
   `xcheck(rindex);
   `xcheck(wctr_r);
   `xcheck(rbank_r);
   `xcheck(cmd_exe);
   `xcheck(cmd_err);
   `xcheck(start);
   `xcheck(stop);
   `xcheck(irqack);
   `xcheck(play_r);
   `xcheck(clr);
   `xcheck(clr_err);
   `xcheck(cfg_err);
   `xcheck(req_r);
   `xcheck(rctr_r);
   `xcheck(irq_r);
   `xcheck(irq_err);
`endif

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 2. Blackbox (functional) assumptions and assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

 `include "apb_assumes.svh"
 
   // req_in_pulse : f_req_in_pulse
   
   property f_req_in_pulse;
      @(posedge clk ) disable iff (rst_n == '0)
	(req_in) |=> (!req_in);
   endproperty

   mf_req_in_pulse: assume property(f_req_in_pulse) else assert_error("mf_req_in_pulse");


   // req_in_first : f_req_in_first

   property f_req_in_first;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_out == 1'b1) |=> (!req_in) [*2];
   endproperty

   mf_req_in_first: assume property(f_req_in_first) 
   else assert_error("mf_req_in_first");


   // cmd_wait_states : f_cmd_wait_states

   property f_cmd_wait_states;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cmd_wait_states: assert property(f_cmd_wait_states) else assert_error("af_cmd_wait_states");
   cf_cmd_wait_states: cover property(f_cmd_wait_states);

   // cmd_wait_states : f_no_wait_states

   property f_no_wait_states;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_no_wait_states: assert property(f_no_wait_states) else assert_error("af_no_wait_states");
   cf_no_wait_states: cover property(f_no_wait_states);

   // register_bank : f_prdata_off

   property f_prdata_off;
      @(posedge clk ) disable iff (rst_n == '0)
	(PSEL == '0) |-> (PRDATA == '0);
   endproperty

   af_prdata_off: assert property(f_prdata_off) else assert_error("af_prdata_off");
   cf_prdata_off: cover property(f_prdata_off);

   // pslverr : f_pslverr_off

   property f_pslverr_off;
      @(posedge clk ) disable iff (rst_n == '0)
	PSLVERR == '0;
   endproperty

   af_pslverr_off: assert property(f_pslverr_off) else assert_error("af_pslverr_off");
   cf_pslverr_off: cover property(f_pslverr_off);

   // cmd_clr, cmd_exe,  : f_clr_out_rise

   property f_clr_out_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_clr_out_rise: assert property(f_clr_out_rise) else assert_error("af_clr_out_rise");
   cf_clr_out_rise: cover property(f_clr_out_rise);

   // cmd_clr, cmd_exe,  : f_clr_out_valid_high

   property f_clr_out_valid_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_clr_out_valid_high: assert property(f_clr_out_valid_high) else assert_error("af_clr_out_valid_high");
   cf_clr_out_valid_high: cover property(f_clr_out_valid_high);

   // cmd_cfg : f_cfg_out_rise

   property f_cfg_out_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cfg_out_rise: assert property(f_cfg_out_rise) else assert_error("af_cfg_out_rise");
   cf_cfg_out_rise: cover property(f_cfg_out_rise);

   // cmd_cfg, cmd_exe : f_cfg_out_valid_high

   property f_cfg_out_valid_high;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cfg_out_valid_high: assert property(f_cfg_out_valid_high) else assert_error("af_cfg_out_valid_high");
   cf_cfg_out_valid_high: cover property(f_cfg_out_valid_high);

   // cmd_start, cmd_exe : f_start_play_out

   property f_start_play_out;
      @(posedge clk ) disable iff (rst_n == '0)
	(PSEL && !PENABLE && PWRITE && (PWDATA == CMD_START)) |=> (play_out);
   endproperty

   af_start_play_out: assert property(f_start_play_out) else assert_error("af_start_play_out");
   cf_start_play_out: cover property(f_start_play_out);

   // cmd_start, cmd_exe : f_play_out_valid_start

   property f_play_out_valid_start;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_play_out_valid_start: assert property(f_play_out_valid_start) else assert_error("af_play_out_valid_start");
   cf_play_out_valid_start: cover property(f_play_out_valid_start);

   // cmd_stop, cmd_exe : f_stop_play_out

   property f_stop_play_out;
      @(posedge clk ) disable iff (rst_n == '0)
	(PSEL && !PENABLE && PWRITE && (PWDATA == CMD_STOP)) |=> (play_out == '0);
   endproperty

   af_stop_play_out: assert property(f_stop_play_out) else assert_error("af_stop_play_out");
   cf_stop_play_out: cover property(f_stop_play_out);

   // cmd_stop, cmd_exe : f_play_out_valid_stop

   property f_play_out_valid_stop;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_play_out_valid_stop: assert property(f_play_out_valid_stop) else assert_error("af_play_out_valid_stop");
   cf_play_out_valid_stop: cover property(f_play_out_valid_stop);

   // cmd_level : f_level_out_rise

   property f_level_out_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_exe && (PWDATA == CMD_LEVEL)) |-> $rose(level_out);
   endproperty

   af_level_out_rise: assert property(f_level_out_rise) else assert_error("af_level_out_rise");
   cf_level_out_rise: cover property(f_level_out_rise);
   
   // cmd_level, cmd_exe : f_level_out_valid_high

   property f_level_out_valid_high;
      @(posedge clk ) disable iff (rst_n == '0)
	(level_out == 1'b1) |-> (PSEL && PENABLE && PWRITE && PREADY && (PWDATA == CMD_LEVEL));
   endproperty

   af_level_out_valid_high: assert property(f_level_out_valid_high) else assert_error("af_level_out_valid_high");
   cf_level_out_valid_high: cover property(f_level_out_valid_high);

   // streaming_standby : f_tick_standby

   property f_tick_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	(!play_out) |-> (!tick_out);
   endproperty

   af_tick_standby: assert property(f_tick_standby) else assert_error("af_tick_standby");
   cf_tick_standby: cover property(f_tick_standby);

   // streaming_tick : f_tick_out_high

   property f_tick_out_high;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_out && req_in && play_out) |=> (tick_out);
   endproperty

   af_tick_out_high: assert property(f_tick_out_high) else assert_error("af_tick_out_high");
   cf_tick_out_high: cover property(f_tick_out_high);

   // streaming_tick : f_tick_out_low

   property f_tick_out_low;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_out == '0 || !req_in || !play_out) |-> (tick_out == '0);
   endproperty

   af_tick_out_low: assert property(f_tick_out_low) else assert_error("af_tick_out_low");
   cf_tick_out_low: cover property(f_tick_out_low);

   // interrupt_logic, irq_out : f_irq_out_raised

   property f_irq_out_raised;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_raised: assert property(f_irq_out_raised) else assert_error("af_irq_out_raised");
   cf_irq_out_raised: cover property(f_irq_out_raised);

   // interrupt_logic, irq_out : f_irq_out_standby

   property f_irq_out_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	(!play_out) |-> (!irq_out);
   endproperty

   af_irq_out_standby: assert property(f_irq_out_standby) else assert_error("af_irq_out_standby");
   cf_irq_out_standby: cover property(f_irq_out_standby);

   // irq_out_rise_first : f_irq_out_rise_first

   property f_irq_out_rise_first;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_rise_first: assert property(f_irq_out_rise_first) else assert_error("af_irq_out_rise_first");
   cf_irq_out_rise_first: cover property(f_irq_out_rise_first);

   // irq_out_rise_other : f_irq_out_rise_other

   property f_irq_out_rise_other;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_irq_out_rise_other: assert property(f_irq_out_rise_other) else assert_error("af_irq_out_rise_other");
   cf_irq_out_rise_other: cover property(f_irq_out_rise_other);

   // irq_out_fall, cmd_irqack : f_irq_out_fall

   property f_irq_out_fall;
      @(posedge clk ) disable iff (rst_n == '0)
	(PSEL && !PENABLE && PWRITE && (PWDATA == CMD_IRQACK || PWDATA == CMD_STOP)) |=> (irq_out == '0);
   endproperty

   af_irq_out_fall: assert property(f_irq_out_fall) else assert_error("af_irq_out_fall");
   cf_irq_out_fall: cover property(f_irq_out_fall);

   // cfg_reg_out_conn : f_cfg_reg_outconn

   property f_cfg_reg_outconn;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_cfg_reg_outconn: assert property(f_cfg_reg_outconn) else assert_error("af_cfg_reg_outconn");
   cf_cfg_reg_outconn: cover property(f_cfg_reg_outconn);

   // level_reg_out_conn : f_level_reg_outconn

   property f_level_reg_outconn;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_level_reg_outconn: assert property(f_level_reg_outconn) else assert_error("af_level_reg_outconn");
   cf_level_reg_outconn: cover property(f_level_reg_outconn);

   // dsp_regs_out_conn : f_dsp_regs_outconn

   property f_dsp_regs_outconn;
      @(posedge clk ) disable iff (rst_n == '0)
	1;
   endproperty

   af_dsp_regs_outconn: assert property(f_dsp_regs_outconn) else assert_error("af_dsp_regs_outconn");
   cf_dsp_regs_outconn: cover property(f_dsp_regs_outconn);

   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 3. Whitebox (RTL) assertions
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


`ifndef SYSTEMC_DUT

   // PSLVERR : r_pslverr

   property r_pslverr;
      @(posedge clk ) disable iff (rst_n == '0)
	!PSLVERR;
   endproperty

   ar_pslverr: assert property(r_pslverr) else assert_error("ar_pslverr");
   cr_pslverr: cover property(r_pslverr);

   // rindex : r_rindex_on

   property r_rindex_on;
      @(posedge clk ) disable iff (rst_n == '0)
	PSEL |-> (rindex == PADDR[RINDEX_BITS+1:2]);
   endproperty

   ar_rindex_on: assert property(r_rindex_on) else assert_error("ar_rindex_on");
   cr_rindex_on: cover property(r_rindex_on);

   // rindex : r_rindex_off

   property r_rindex_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!PSEL |-> (rindex == 0);
   endproperty

   ar_rindex_off: assert property(r_rindex_off) else assert_error("ar_rindex_off");
   cr_rindex_off: cover property(r_rindex_off);

   // rindex : r_index_range

   property r_index_range;
      @(posedge clk ) disable iff (rst_n == '0)
	rindex >= 0 && rindex < AUDIOPORT_REGISTERS;
   endproperty

   ar_index_range: assert property(r_index_range) else assert_error("ar_index_range");
   cr_index_range: cover property(r_index_range);

   // wctr_r : r_wctr_r_start

   property r_wctr_r_start;
      @(posedge clk ) disable iff (rst_n == '0)
	(wctr_r == 0) && (PSEL && !PENABLE && PWRITE && (rindex == CMD_REG_INDEX)) |=> (wctr_r == 1);
   endproperty

   ar_wctr_r_start: assert property(r_wctr_r_start) else assert_error("ar_wctr_r_start");
   cr_wctr_r_start: cover property(r_wctr_r_start);

   // wctr_r : r_wctr_r_zero

   property r_wctr_r_zero;
      @(posedge clk ) disable iff (rst_n == '0)
	(!PSEL || !PWRITE || (rindex != CMD_REG_INDEX)) |=> (wctr_r == 0);
   endproperty

   ar_wctr_r_zero: assert property(r_wctr_r_zero) else assert_error("ar_wctr_r_zero");
   cr_wctr_r_zero: cover property(r_wctr_r_zero);

   // wctr_r : r_wctr_r_inc

   property r_wctr_r_inc;
      @(posedge clk ) disable iff (rst_n == '0)
	(wctr_r > 0) && (wctr_r < CMD_WAIT_STATES) && (PSEL && PENABLE && PWRITE && (rindex == CMD_REG_INDEX)) |=> wctr_r == $past(wctr_r) + 1;
   endproperty

   ar_wctr_r_inc: assert property(r_wctr_r_inc) else assert_error("ar_wctr_r_inc");
   cr_wctr_r_inc: cover property(r_wctr_r_inc);

   // wctr_r : r_wctr_r_stop

   property r_wctr_r_stop;
      @(posedge clk ) disable iff (rst_n == '0)
	(wctr_r == CMD_WAIT_STATES) |=> (wctr_r == 0);
   endproperty

   ar_wctr_r_stop: assert property(r_wctr_r_stop) else assert_error("ar_wctr_r_stop");
   cr_wctr_r_stop: cover property(r_wctr_r_stop);

   // rbank_r : r_rbank_r_write

   property r_rbank_r_write;
      @(posedge clk ) disable iff (rst_n == '0)
	(PSEL && PENABLE && PWRITE && (wctr_r == 0)) |=> rbank_r[$past(rindex)] == $past(PWDATA);
   endproperty

   ar_rbank_r_write: assert property(r_rbank_r_write) else assert_error("ar_rbank_r_write");
   cr_rbank_r_write: cover property(r_rbank_r_write);

   // rbank_r : r_rbank_r_clr

   property r_rbank_r_clr;
      @(posedge clk ) disable iff (rst_n == '0)
	clr |=> rbank_r[ABUF1_END_INDEX:ABUF0_START_INDEX] == 0;
   endproperty

   ar_rbank_r_clr: assert property(r_rbank_r_clr) else assert_error("ar_rbank_r_clr");
   cr_rbank_r_clr: cover property(r_rbank_r_clr);

   // rbank_r : r_status_reg_play

   property r_status_reg_play;
      @(posedge clk ) disable iff (rst_n == '0)
	start |=> rbank_r[STATUS_REG_INDEX][STATUS_PLAY] == '1;
   endproperty

   ar_status_reg_play: assert property(r_status_reg_play) else assert_error("ar_status_reg_play");
   cr_status_reg_play: cover property(r_status_reg_play);

   // rbank_r : r_status_reg_standby

   property r_status_reg_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	stop |=> rbank_r[STATUS_REG_INDEX][STATUS_PLAY] == '0;
   endproperty

   ar_status_reg_standby: assert property(r_status_reg_standby) else assert_error("ar_status_reg_standby");
   cr_status_reg_standby: cover property(r_status_reg_standby);

   // rbank_r : r_status_clr_err

   property r_status_clr_err;
      @(posedge clk ) disable iff (rst_n == '0)
	clr_err |=> rbank_r[STATUS_REG_INDEX][STATUS_CLR_ERR] == '1;
   endproperty

   ar_status_clr_err: assert property(r_status_clr_err) else assert_error("ar_status_clr_err");
   cr_status_clr_err: cover property(r_status_clr_err);

   // rbank_r : r_status_cfg_err

   property r_status_cfg_err;
      @(posedge clk ) disable iff (rst_n == '0)
	cfg_err |=> rbank_r[STATUS_REG_INDEX][STATUS_CFG_ERR] == '1;
   endproperty

   ar_status_cfg_err: assert property(r_status_cfg_err) else assert_error("ar_status_cfg_err");
   cr_status_cfg_err: cover property(r_status_cfg_err);

   // rbank_r : r_status_irq_err

   property r_status_irq_err;
      @(posedge clk ) disable iff (rst_n == '0)
	irq_err && !(PSEL && PENABLE && PWRITE && (wctr_r == 0) && (rindex == STATUS_REG_INDEX)) |=>   rbank_r[STATUS_REG_INDEX][STATUS_IRQ_ERR] == '1;
   endproperty

   ar_status_irq_err: assert property(r_status_irq_err) else assert_error("ar_status_irq_err");
   cr_status_irq_err: cover property(r_status_irq_err);

   // rbank_r : r_status_cmd_err

   property r_status_cmd_err;
      @(posedge clk ) disable iff (rst_n == '0)
	cmd_err |=> rbank_r[STATUS_REG_INDEX][STATUS_CMD_ERR] == '1;
   endproperty

   ar_status_cmd_err: assert property(r_status_cmd_err) else assert_error("ar_status_cmd_err");
   cr_status_cmd_err: cover property(r_status_cmd_err);

   // rbank_r : r_rbank_r_stable

   property r_rbank_r_stable;
      @(posedge clk ) disable iff (rst_n == '0)
	!((PSEL && PENABLE && PWRITE) || clr || start || stop || clr_err || cfg_err || irq_err || cmd_err) |=> $stable(rbank_r);
   endproperty

   ar_rbank_r_stable: assert property(r_rbank_r_stable) else assert_error("ar_rbank_r_stable");
   cr_rbank_r_stable: cover property(r_rbank_r_stable);

   // rbank_r : r_status_reg_stable

   property r_status_reg_stable;
      @(posedge clk ) disable iff (rst_n == '0)
	!((wctr_r == 0) && PSEL && PENABLE && PWRITE && (rindex == STATUS_REG_INDEX)) && !start && !stop && !clr_err && !cfg_err && !irq_err && !cmd_err |=> $stable(rbank_r[STATUS_REG_INDEX]);
   endproperty

   ar_status_reg_stable: assert property(r_status_reg_stable) else assert_error("ar_status_reg_stable");
   cr_status_reg_stable: cover property(r_status_reg_stable);

   // rbank_r : r_abuf_regs_stable

   property r_abuf_regs_stable;
      @(posedge clk ) disable iff (rst_n == '0)
	!(((wctr_r == 0) && PSEL && PENABLE && PWRITE && (rindex >= ABUF0_START_INDEX) && (rindex <= ABUF1_END_INDEX)) || clr) |=> $stable(rbank_r[ABUF1_END_INDEX:ABUF0_START_INDEX]);
   endproperty

   ar_abuf_regs_stable: assert property(r_abuf_regs_stable) else assert_error("ar_abuf_regs_stable");
   cr_abuf_regs_stable: cover property(r_abuf_regs_stable);

   // cfg_reg_out : r_cfg_reg_out

   property r_cfg_reg_out;
      @(posedge clk ) disable iff (rst_n == '0)
	cfg_reg_out == rbank_r[CFG_REG_INDEX];
   endproperty

   ar_cfg_reg_out: assert property(r_cfg_reg_out) else assert_error("ar_cfg_reg_out");
   cr_cfg_reg_out: cover property(r_cfg_reg_out);

   // level_reg_out : r_level_reg_out

   property r_level_reg_out;
      @(posedge clk ) disable iff (rst_n == '0)
	level_reg_out == rbank_r[LEVEL_REG_INDEX];
   endproperty

   ar_level_reg_out: assert property(r_level_reg_out) else assert_error("ar_level_reg_out");
   cr_level_reg_out: cover property(r_level_reg_out);

   // dsp_regs_out : r_dsp_regs_out

   property r_dsp_regs_out;
      @(posedge clk ) disable iff (rst_n == '0)
	dsp_regs_out == rbank_r[DSP_REGS_END_INDEX:DSP_REGS_START_INDEX];
   endproperty

   ar_dsp_regs_out: assert property(r_dsp_regs_out) else assert_error("ar_dsp_regs_out");
   cr_dsp_regs_out: cover property(r_dsp_regs_out);

   // PRDATA : r_prdata_read

   property r_prdata_read;
      @(posedge clk ) disable iff (rst_n == '0)
	PSEL |-> PRDATA == rbank_r[rindex];
   endproperty

   ar_prdata_read: assert property(r_prdata_read) else assert_error("ar_prdata_read");
   cr_prdata_read: cover property(r_prdata_read);

   // PRDATA : r_prdata_off

   property r_prdata_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!PSEL |-> PRDATA == 0;
   endproperty

   ar_prdata_off: assert property(r_prdata_off) else assert_error("ar_prdata_off");
   cr_prdata_off: cover property(r_prdata_off);

   // play_r : r_play_r_rise

   property r_play_r_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	start |=> play_r;
   endproperty

   ar_play_r_rise: assert property(r_play_r_rise) else assert_error("ar_play_r_rise");
   cr_play_r_rise: cover property(r_play_r_rise);

   // play_r : r_play_r_fall

   property r_play_r_fall;
      @(posedge clk ) disable iff (rst_n == '0)
	stop |=> !play_r;
   endproperty

   ar_play_r_fall: assert property(r_play_r_fall) else assert_error("ar_play_r_fall");
   cr_play_r_fall: cover property(r_play_r_fall);

   // play_r : r_play_r_stable

   property r_play_r_stable;
      @(posedge clk ) disable iff (rst_n == '0)
	(!start && !stop) |=> $stable(play_r);
   endproperty

   ar_play_r_stable: assert property(r_play_r_stable) else assert_error("ar_play_r_stable");
   cr_play_r_stable: cover property(r_play_r_stable);

   // play_out : r_play_out_state

   property r_play_out_state;
      @(posedge clk ) disable iff (rst_n == '0)
	play_out == play_r;
   endproperty

   ar_play_out_state: assert property(r_play_out_state) else assert_error("ar_play_out_state");
   cr_play_out_state: cover property(r_play_out_state);

   // cmd_exe : r_cmd_exe_on

   property r_cmd_exe_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(PSEL && PENABLE && PWRITE && (wctr_r == 0) && (rindex == CMD_REG_INDEX)) |-> cmd_exe;
   endproperty

   ar_cmd_exe_on: assert property(r_cmd_exe_on) else assert_error("ar_cmd_exe_on");
   cr_cmd_exe_on: cover property(r_cmd_exe_on);

   // cmd_exe : r_cmd_exe_off

   property r_cmd_exe_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(PSEL && PENABLE && PWRITE && (wctr_r == 0) && (rindex == CMD_REG_INDEX)) |-> !cmd_exe;
   endproperty

   ar_cmd_exe_off: assert property(r_cmd_exe_off) else assert_error("ar_cmd_exe_off");
   cr_cmd_exe_off: cover property(r_cmd_exe_off);

   // cmd_err : r_cmd_err_on

   property r_cmd_err_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_exe && !(PWDATA inside {CMD_NOP, CMD_CLR, CMD_CFG, CMD_START, CMD_STOP, CMD_LEVEL, CMD_IRQACK})) |-> cmd_err;
   endproperty

   ar_cmd_err_on: assert property(r_cmd_err_on) else assert_error("ar_cmd_err_on");
   cr_cmd_err_on: cover property(r_cmd_err_on);

   // cmd_err : r_cmd_err_off

   property r_cmd_err_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(cmd_exe && !(PWDATA inside {CMD_NOP, CMD_CLR, CMD_CFG, CMD_START, CMD_STOP, CMD_LEVEL, CMD_IRQACK}))|-> !cmd_err;
   endproperty

   ar_cmd_err_off: assert property(r_cmd_err_off) else assert_error("ar_cmd_err_off");
   cr_cmd_err_off: cover property(r_cmd_err_off);

   // clr : r_clr_on

   property r_clr_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(!play_r && cmd_exe && (PWDATA == CMD_CLR)) |-> clr;
   endproperty

   ar_clr_on: assert property(r_clr_on) else assert_error("ar_clr_on");
   cr_clr_on: cover property(r_clr_on);

   // clr : r_clr_off

   property r_clr_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(!play_r && cmd_exe && (PWDATA == CMD_CLR)) |-> !clr;
   endproperty

   ar_clr_off: assert property(r_clr_off) else assert_error("ar_clr_off");
   cr_clr_off: cover property(r_clr_off);

   // clr_out : r_clr_out

   property r_clr_out;
      @(posedge clk ) disable iff (rst_n == '0)
	clr_out == clr;
   endproperty

   ar_clr_out: assert property(r_clr_out) else assert_error("ar_clr_out");
   cr_clr_out: cover property(r_clr_out);

   // clr_err : r_clr_err_on

   property r_clr_err_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_r && cmd_exe && (PWDATA == CMD_CLR)) |-> clr_err;
   endproperty

   ar_clr_err_on: assert property(r_clr_err_on) else assert_error("ar_clr_err_on");
   cr_clr_err_on: cover property(r_clr_err_on);

   // clr_err : r_clr_err_off

   property r_clr_err_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(play_r && cmd_exe && (PWDATA == CMD_CLR)) |-> !clr_err;
   endproperty

   ar_clr_err_off: assert property(r_clr_err_off) else assert_error("ar_clr_err_off");
   cr_clr_err_off: cover property(r_clr_err_off);

   // cfg_out : r_cfg_out_on

   property r_cfg_out_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(!play_r && cmd_exe && (PWDATA == CMD_CFG) ) |-> cfg_out;
   endproperty

   ar_cfg_out_on: assert property(r_cfg_out_on) else assert_error("ar_cfg_out_on");
   cr_cfg_out_on: cover property(r_cfg_out_on);

   // cfg_out : r_cfg_out_off

   property r_cfg_out_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(!play_r && cmd_exe && (PWDATA == CMD_CFG) ) |-> !cfg_out;
   endproperty

   ar_cfg_out_off: assert property(r_cfg_out_off) else assert_error("ar_cfg_out_off");
   cr_cfg_out_off: cover property(r_cfg_out_off);

   // cfg_err : r_cfg_err_on

   property r_cfg_err_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_r && cmd_exe && (PWDATA == CMD_CFG) ) |-> cfg_err;
   endproperty

   ar_cfg_err_on: assert property(r_cfg_err_on) else assert_error("ar_cfg_err_on");
   cr_cfg_err_on: cover property(r_cfg_err_on);

   // cfg_err : r_cfg_err_off

   property r_cfg_err_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(play_r && cmd_exe && (PWDATA == CMD_CFG) ) |-> !cfg_err;
   endproperty

   ar_cfg_err_off: assert property(r_cfg_err_off) else assert_error("ar_cfg_err_off");
   cr_cfg_err_off: cover property(r_cfg_err_off);

   // start : r_start_on

   property r_start_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_exe && (PWDATA == CMD_START) ) |-> start;
   endproperty

   ar_start_on: assert property(r_start_on) else assert_error("ar_start_on");
   cr_start_on: cover property(r_start_on);

   // start : r_start_off

   property r_start_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(cmd_exe && (PWDATA == CMD_START) ) |-> !start;
   endproperty

   ar_start_off: assert property(r_start_off) else assert_error("ar_start_off");
   cr_start_off: cover property(r_start_off);

   // stop : r_stop_on

   property r_stop_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_exe && (PWDATA == CMD_STOP) ) |-> stop;
   endproperty

   ar_stop_on: assert property(r_stop_on) else assert_error("ar_stop_on");
   cr_stop_on: cover property(r_stop_on);

   // stop : r_stop_off

   property r_stop_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(cmd_exe && (PWDATA == CMD_STOP) ) |-> !stop;
   endproperty

   ar_stop_off: assert property(r_stop_off) else assert_error("ar_stop_off");
   cr_stop_off: cover property(r_stop_off);

   // level_out : r_level_out_on

   property r_level_out_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_exe && (PWDATA == CMD_LEVEL) ) |-> level_out;
   endproperty

   ar_level_out_on: assert property(r_level_out_on) else assert_error("ar_level_out_on");
   cr_level_out_on: cover property(r_level_out_on);

   // level_out : r_level_out_off

   property r_level_out_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(cmd_exe && (PWDATA == CMD_LEVEL) ) |-> !level_out;
   endproperty

   ar_level_out_off: assert property(r_level_out_off) else assert_error("ar_level_out_off");
   cr_level_out_off: cover property(r_level_out_off);

   // irqack : r_irqack_on

   property r_irqack_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(cmd_exe && (PWDATA == CMD_IRQACK) ) |-> irqack;
   endproperty

   ar_irqack_on: assert property(r_irqack_on) else assert_error("ar_irqack_on");
   cr_irqack_on: cover property(r_irqack_on);

   // irqack : r_irqack_off

   property r_irqack_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(cmd_exe && (PWDATA == CMD_IRQACK) ) |-> !irqack;
   endproperty

   ar_irqack_off: assert property(r_irqack_off) else assert_error("ar_irqack_off");
   cr_irqack_off: cover property(r_irqack_off);

   // rctr_r : r_rctr_r_standby

   property r_rctr_r_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	!play_r  |-> (rctr_r == 0);
   endproperty

   ar_rctr_r_standby: assert property(r_rctr_r_standby) else assert_error("ar_rctr_r_standby");
   cr_rctr_r_standby: cover property(r_rctr_r_standby);

   // rctr_r : r_rctr_r_stop

   property r_rctr_r_stop;
      @(posedge clk ) disable iff (rst_n == '0)
	stop |=> rctr_r == 0;
   endproperty

   ar_rctr_r_stop: assert property(r_rctr_r_stop) else assert_error("ar_rctr_r_stop");
   cr_rctr_r_stop: cover property(r_rctr_r_stop);

   // rctr_r : r_rctr_r_inc

   property r_rctr_r_inc;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_r && !stop && req_r && (rctr_r < ABUF_REGISTERS-2)) |=> (rctr_r == $past(rctr_r)+2);
   endproperty

   ar_rctr_r_inc: assert property(r_rctr_r_inc) else assert_error("ar_rctr_r_inc");
   cr_rctr_r_inc: cover property(r_rctr_r_inc);

   // rctr_r : r_rctr_r_roll

   property r_rctr_r_roll;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_r && !stop && req_r && (rctr_r >= ABUF_REGISTERS-2)) |=> (rctr_r == 0);
   endproperty

   ar_rctr_r_roll: assert property(r_rctr_r_roll) else assert_error("ar_rctr_r_roll");
   cr_rctr_r_roll: cover property(r_rctr_r_roll);

   // rctr_r : rctr_r_stable

   property rctr_r_stable;
      @(posedge clk ) disable iff (rst_n == '0)
	(play_r && !stop && !req_r) |=> $stable(rctr_r);
   endproperty

   arctr_r_stable: assert property(rctr_r_stable) else assert_error("arctr_r_stable");
   crctr_r_stable: cover property(rctr_r_stable);

   // audio0_out : r_audio0_out

   property r_audio0_out;
      @(posedge clk ) disable iff (rst_n == '0)
	audio0_out == rbank_r[rctr_r + ABUF0_START_INDEX][23:0];
   endproperty

   ar_audio0_out: assert property(r_audio0_out) else assert_error("ar_audio0_out");
   cr_audio0_out: cover property(r_audio0_out);

   // audio1_out : r_audio1_out

   property r_audio1_out;
      @(posedge clk ) disable iff (rst_n == '0)
	audio1_out ==rbank_r[rctr_r + ABUF0_START_INDEX+1][23:0];
   endproperty

   ar_audio1_out: assert property(r_audio1_out) else assert_error("ar_audio1_out");
   cr_audio1_out: cover property(r_audio1_out);

   // tick_out : r_tick_out_standby

   property r_tick_out_standby;
      @(posedge clk ) disable iff (rst_n == '0)
	!play_r |-> !tick_out;
   endproperty

   ar_tick_out_standby: assert property(r_tick_out_standby) else assert_error("ar_tick_out_standby");
   cr_tick_out_standby: cover property(r_tick_out_standby);

   // tick_out : r_tick_out_play

   property r_tick_out_play;
      @(posedge clk ) disable iff (rst_n == '0)
	play_r |-> (tick_out == req_r);
   endproperty

   ar_tick_out_play: assert property(r_tick_out_play) else assert_error("ar_tick_out_play");
   cr_tick_out_play: cover property(r_tick_out_play);

   // req_r : r_req_r

   property r_req_r;
      @(posedge clk ) disable iff (rst_n == '0)
	play_r |=> req_r == $past(req_in);
   endproperty

   ar_req_r: assert property(r_req_r) else assert_error("ar_req_r");
   cr_req_r: cover property(r_req_r);

   // irq_r : r_irq_r_rise

   property r_irq_r_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	(req_r && play_r && !stop && !irqack &&  ((rctr_r == 2*AUDIO_BUFFER_SIZE-2) || (rctr_r == 4*AUDIO_BUFFER_SIZE-2))) |=> irq_r;
   endproperty

   ar_irq_r_rise: assert property(r_irq_r_rise) else assert_error("ar_irq_r_rise");
   cr_irq_r_rise: cover property(r_irq_r_rise);

   // irq_r : r_irq_r_fall_stop

   property r_irq_r_fall_stop;
      @(posedge clk ) disable iff (rst_n == '0)
	stop |=> !irq_r;
   endproperty

   ar_irq_r_fall_stop: assert property(r_irq_r_fall_stop) else assert_error("ar_irq_r_fall_stop");
   cr_irq_r_fall_stop: cover property(r_irq_r_fall_stop);

   // irq_r : r_irq_r_fall_irqack

   property r_irq_r_fall_irqack;
      @(posedge clk ) disable iff (rst_n == '0)
	irqack |=> !irq_r;
   endproperty

   ar_irq_r_fall_irqack: assert property(r_irq_r_fall_irqack) else assert_error("ar_irq_r_fall_irqack");
   cr_irq_r_fall_irqack: cover property(r_irq_r_fall_irqack);

   // irq_out : r_irq_out

   property r_irq_out;
      @(posedge clk ) disable iff (rst_n == '0)
	irq_out == irq_r;
   endproperty

   ar_irq_out: assert property(r_irq_out) else assert_error("ar_irq_out");
   cr_irq_out: cover property(r_irq_out);

   // irq_err : r_irq_err_on

   property r_irq_err_on;
      @(posedge clk ) disable iff (rst_n == '0)
	(irq_r && req_r && play_r && !stop && !irqack && ((rctr_r == 2*AUDIO_BUFFER_SIZE-2) || (rctr_r == 4*AUDIO_BUFFER_SIZE-2))) |-> irq_err;
   endproperty

   ar_irq_err_on: assert property(r_irq_err_on) else assert_error("ar_irq_err_on");
   cr_irq_err_on: cover property(r_irq_err_on);

   // irq_err : r_irq_err_off

   property r_irq_err_off;
      @(posedge clk ) disable iff (rst_n == '0)
	!(irq_r && req_r && play_r && !stop && !irqack && ((rctr_r == 2*AUDIO_BUFFER_SIZE-2) || (rctr_r == 4*AUDIO_BUFFER_SIZE-2))) |-> !irq_err;
   endproperty

   ar_irq_err_off: assert property(r_irq_err_off) else assert_error("ar_irq_err_off");
   cr_irq_err_off: cover property(r_irq_err_off);

`endif //  `ifndef SYSTEMC_DUT
   
   
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
   // 4. Covergroups
   /////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

`ifndef SYSTEMC_DUT
`ifdef RTL_SIM

   // cg_apb_writes

   

   // cg_apb_reads

   

   // cg_apb_commands

   

`endif //  `ifdef RTL_SIM
`endif //  `ifndef SYSTEMC_DUT
   

endmodule




