// assertion_tb.sv: Simple testbench for debugging assertions 
//
// Usage:
//      1. Create a scenario where an assertion a_X based on property X should
//         PASS and FAIL in the initial proceudre below
//      2. Run the script to verify that the waveforms look OK
//         vsim -do scripts/assertion_tb.tcl
//      3. Declare the property and assertions below the initial process
//      4. Run the script again. The script puts all assertions in the Wave window.
//         Expand an assertion (+) and its ActiveCount (+) to view evaluation details
//      5. To get a detailed view of assertion evaluation, do the following:
//         a) Activate the Assertions tab
//         b) Select an assertion
//         c) Using the right button, execure View ATV.. and select a specific
//            passing or failure of the assertion (ATV = assertion thread view)
//         d) You can now follow the evaluation of property expressions in time
// 

import audioport_pkg::*;
import audioport_util_pkg::*;

module assertion_tb; 
   
   // Clock and reset 
   logic clk = '0, rst_n = 0; 
   always #10ns clk = ~clk; 
   initial @(negedge clk) rst_n = '1; 

   logic PSEL;
   logic PENABLE;
   logic PWRITE;
   logic [31:0]  PADDR;
   logic [31:0] PWDATA;
   logic [31:0] PRDATA;
   logic PREADY;
   logic PSLVERR;
   logic irq_out;
   logic [1:0][23:0] abuf_out;
   logic cfg_out;
   logic [31:0] cfg_reg_out;
   logic level_out;
   logic [31:0] level_reg_out;
   logic [DSP_REGISTERS-1:0][31:0] dsp_regs_out;
   logic clr_out;    
   logic tick_out;
   
   ///////////////////////////////////////////////////////////////////
   // Test data generation process 
   ///////////////////////////////////////////////////////////////////

   initial 
     begin

	
	$info("f_cfg_reg_write OK");
	PSEL = '0;
	PENABLE = '0;
	PWRITE = '0;
	PREADY = '0;
	PADDR = CFG_REG_ADDRESS;
	PWDATA = $urandom;
	cfg_reg_out = '0;
	@(negedge clk); 
	PSEL = '1;
	PWRITE = '1;
	PREADY = '1;
	@(negedge clk); 	
	PENABLE = '1;
	@(negedge clk); 	
	PSEL = '0;
	PENABLE = '0;
	PWRITE = '0;
	PREADY = '0;
	cfg_reg_out = PWDATA;
	@(negedge clk);

	#1us;
	
	$info("f_cfg_reg_write FAIL1");
	PSEL = '0;
	PENABLE = '0;
	PWRITE = '0;
	PREADY = '0;
	PADDR = CFG_REG_ADDRESS;
	PWDATA = $urandom;
	@(negedge clk); 
	PSEL = '1;
	PWRITE = '1;
	PREADY = '1;
	@(negedge clk); 	
	PENABLE = '1;
	@(negedge clk); 	
	PSEL = '0;
	PENABLE = '0;
	PWRITE = '0;
	PREADY = '0;
	@(negedge clk); // One cycle too late	
	cfg_reg_out = PWDATA;
	@(negedge clk);

	
	#1us;
	
	$info("f_cfg_reg_write FAIL2");
	PSEL = '0;
	PENABLE = '0;
	PWRITE = '0;
	PREADY = '0;
	PADDR = CFG_REG_ADDRESS;
	PWDATA = $urandom;
	@(negedge clk); 
	PSEL = '1;
	PWRITE = '1;
	PREADY = '1;
	@(negedge clk); 	
	PENABLE = '1;
	@(negedge clk); 	
	PSEL = '0;
	PENABLE = '0;
	PWRITE = '0;
	PREADY = '0;
	cfg_reg_out = PWDATA ^ 32'h00000001; // Wrong data
	@(negedge clk);

	#1us;
	
	$finish;
	
     end 
   
   ///////////////////////////////////////////////////////////////////
   // Properties and assertions
   ///////////////////////////////////////////////////////////////////

   
   // ---------------------------------------------------------------------------      
   // f_cfg_reg_write
   // ---------------------------------------------------------------------------

   property f_cfg_reg_write;
      @(posedge clk) disable iff (rst_n == '0)
        PSEL && PENABLE && PREADY && PWRITE && (PADDR == CFG_REG_ADDRESS) |=> cfg_reg_out == $past(PWDATA);
   endproperty
      
   af_cfg_reg_write: assert property(f_cfg_reg_write)
     else assert_error("f_cfg_reg_out");
   cf_cfg_reg_write: cover property(f_cfg_reg_write);
      
endmodule 
