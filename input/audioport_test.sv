`include "audioport.svh"

import audioport_pkg::*;
import audioport_util_pkg::*;

program audioport_test
  
  (input logic clk,
   input logic 	rst_n,
   input logic 	mclk,
		apb_if apb,
		irq_out_if irq,
		i2s_if i2s, 
   output logic test_mode_in,
   output logic scan_en_in,   
   input logic 	sck_out,
   input logic 	ws_out,
   input logic 	sdo_out
   );

   initial
     begin : test_program
	logic         fail;
	logic [31:0]  addr;
	logic [31:0]  wdata;
	
	scan_en_in = '0;
	test_mode_in = '0;	
	apb.init;
	wait(rst_n);

	
	/////////////////////////////////////////////////////////////////
	// Fill data registers
	/////////////////////////////////////////////////////////////////	

	for (int i=0; i < ABUF_REGISTERS; ++i)
	  begin
	     wdata = $urandom;
	     apb.write(ABUF0_START_ADDRESS + 4*i, wdata, fail);
	  end

	for (int i=0; i < DSP_REGISTERS; ++i)
	  begin
	     wdata = $urandom;
	     apb.write(DSP_REGS_START_ADDRESS + 4*i, wdata, fail);
	  end
	
	/////////////////////////////////////////////////////////////////
	// Configure: 192 kHz, filter ON, stereo
	/////////////////////////////////////////////////////////////////	

	addr = CFG_REG_ADDRESS;
	wdata = 32'b00000000_00000000_00000000_00001010;
	apb.write(addr, wdata, fail);	 	

	addr = CMD_REG_ADDRESS;
	wdata = CMD_CFG;
	apb.write(addr, wdata, fail);	 	

	/////////////////////////////////////////////////////////////////
	// Full volume
	/////////////////////////////////////////////////////////////////	
	
	addr = LEVEL_REG_ADDRESS;
	wdata = 32'h80008000;
	apb.write(addr, wdata, fail);	 	

	addr = CMD_REG_ADDRESS;
	wdata = CMD_LEVEL;
	apb.write(addr, wdata, fail);	 	
	
	/////////////////////////////////////////////////////////////////
	// Play
	/////////////////////////////////////////////////////////////////	

	addr = CMD_REG_ADDRESS;
	wdata = CMD_START;
	apb.write(addr, wdata, fail);	 	

	#200us;

	/////////////////////////////////////////////////////////////////
	// Stop
	/////////////////////////////////////////////////////////////////	
	
	addr = CMD_REG_ADDRESS;
	wdata = CMD_STOP;
	apb.write(addr, wdata, fail);	     

	#10us;


	/////////////////////////////////////////////////////////////////
	// Test mode
	/////////////////////////////////////////////////////////////////	
	
	$assertoff;
	
	scan_en_in = '1;
	test_mode_in = '1;	
	
	repeat(6419) begin
	   apb.set(32'hffffffff, 32'hffffffff, '1, '1, '1);	     	   
	   @(negedge clk);
	end
	$info("L");
	
	repeat(6419) begin
	   apb.set(32'h00000000, 32'h00000000, '0, '0, '0);
	   @(negedge clk);
	end

	$info("L");

	repeat(6419) begin
	   apb.set(32'hffffffff, 32'hffffffff, '1, '1, '1);	     	   
	   @(negedge clk);
	end
	$info("L");
	
	$asserton;
	
	$finish;
	
     end : test_program

endprogram
     
