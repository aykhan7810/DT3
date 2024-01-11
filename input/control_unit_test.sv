`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program control_unit_test
  // 1. Ports  
  (input logic clk,
   output logic 		      rst_n,
   apb_if                             apb,
   irq_out_if                         irq,
   input logic [23:0] 		      audio0_out,
   input logic [23:0] 		      audio1_out, 
   input logic 			      cfg_out,
   input logic [31:0] 		      cfg_reg_out,
   input logic 			      level_out,
   input logic [31:0] 		      level_reg_out,
   input logic [DSP_REGISTERS*32-1:0] dsp_regs_out,
   input logic 			      clr_out, 
   input logic 			      tick_out,
   input logic 			      play_out,
   output logic 		      req_in
   );

   // 2. Variable declarations
   logic 				    wfail;
   logic 				    rfail;   
   logic [31:0] 			    addr;
   logic [31:0] 			    wdata;
   logic [31:0] 			    rdata;      

   // 3. Task code inclusion
`include "control_unit_test_tasks.svh"

   // 4. Executable process
   initial
     begin

	// 5. Reset gloal variable used for results tracking
	// See audioport_pkg.sv
	reset_test_stats; 
	
	// 6. Run tests

	reset_test;
	apb_test;
/*	
        address_decoding_test;
	wait_states_test;
	register_test;
	cmd_exe_test;
	cmd_err_test;
	cmd_start_stop_test;
	cmd_level_test;
	cmd_clr_test;
        clr_err_test;
	cmd_cfg_test;
	cfg_err_test;
	abuf_test;
	interrupt_test;
	streaming_test;
	irq_out_stop_test;
	status_reg_write_test;
*/	
	// 7. Report results
	
	$display("#####################################################################################################");	
	$display("control_unit_test results: PASSED: %d / FAILED: %d", tests_passed, tests_failed);
	$display("#####################################################################################################");	
	
	$finish;
	
     end
	
endprogram
