////////////////////////////////////////////////////////////////////////////////////////////////////
task reset_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("reset_test");

   req_in = '0;
   apb.init;
   rst_n = '0;
   @(negedge clk);
   @(negedge clk);   
   rst_n = '1;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task apb_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("apb_test"); // Message to user

   // 1. Execute reset
   reset_test;

   // Fork three concurrent processes
   fork
      begin : apb_control

	 // 2.1.1.
	 addr = AUDIOPORT_START_ADDRESS;
	 wdata = CMD_START;
	 wfail = '0;
	 rfail = '0;
	 apb.write(addr, wdata, wfail);
	 apb.read(addr, rdata, rfail);   
	 ia_apb_test1: assert (!wfail && !rfail) else 
	   assert_error("ia_apb_test");  // See audioport_pkg.sv

	 //2.1.2.	 
	 repeat(30)
	   @(posedge clk);
	 
	 //2.1.3.
	 addr = AUDIOPORT_START_ADDRESS-4;
	 wdata = $urandom;
	 wfail = '0;
	 rfail = '0;
	 apb.write(addr, wdata, wfail);
	 apb.read(addr, rdata, rfail);   
	 ia_apb_test2: assert (!wfail && !rfail) else 
	   assert_error("ia_apb_test");  // See audioport_pkg.sv
      end : apb_control

      begin : req_in_writer

	 // 2-2.1.
	 wait (play_out);
	 
	 // 2-2.2.
	 forever
	   begin
	      repeat(10) @(posedge clk);
	      req_in = '1;
	      @(posedge clk);	      
	      req_in = '0;
	   end
	 
      end : req_in_writer

      begin : irq_out_reader
	 logic irq_out_state;

	 // 2-3.1
	 forever
	   begin
	      @(posedge clk);	      
	      irq.monitor(irq_out_state);
	      if (irq_out_state) 
		$info("irq_out");
	   end
	 
      end : irq_out_reader
   join_any
   disable fork; // Kill all processes if one exits
   
   update_test_stats; // See audioport_pkg.sv

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task address_decoding_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("address_decoding_test");

   //--To do: Write your code between these lines --------------------------------------------------


   //----------------------------------------------------------------------------------------------
   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task wait_states_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("wait_states_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task register_bank_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("register_bank_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_exe_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_exe_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_err_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_err_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_start_stop_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_start_stop_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_level_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_level_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_clr_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_clr_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_cfg_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_cfg_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task clr_err_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("clr_err_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cfg_err_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cfg_err_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task abuf_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("abuf_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task interrupt_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("interrupt_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task streaming_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

/*  Check that the continuous streaming functionality works correctly. */

   int 					    target_abuf;
   int 					    irq_counter;
   logic 				    irq_out_state;
   logic [23:0] 			    stream_wdata;
   logic [23:0] 			    stream_rdata;   
   int 					    cycle_counter;
   
   $info("streamimg_test");   

   // 1.
   reset_test;
   // 2.
   stream_wdata = 1;
   // 3.
   for (int i=0; i < ABUF_REGISTERS; ++i)
     begin
	wdata = stream_wdata;
	apb.write(ABUF0_START_ADDRESS + 4*i, wdata, wfail);
	++stream_wdata;
     end
   
   fork

      begin : apb_control
	 // 4-1.1.
	 addr = CMD_REG_ADDRESS;
	 wdata = CMD_START;
	 apb.write(addr, wdata, wfail);
	 // 4-1.2.
	 #1ms;
	 // 4-1.3.	
	 addr = CMD_REG_ADDRESS;
	 wdata = CMD_STOP;
	 apb.write(addr, wdata, wfail);

      end : apb_control

      begin : interrupt_handler
	 // 4-2.1.	 
	 target_abuf = 0;	 
	 // 4-2.2.	 
	 wait(play_out);

	 while (play_out)
	   begin
	      // 4-2.3.
	      irq_out_state = '0;
	      cycle_counter = 0;
	      while (!irq_out_state) begin
		 irq.monitor(irq_out_state);
		 ++cycle_counter;
		 assert ( cycle_counter < (AUDIO_BUFFER_SIZE+1) * CLK_DIV_48000 )
		   else begin
		      ia_interrupt_timeout: assert_error("ia_interrupt_timeout");
		      break;
		   end
	      end
	      // 4-2.4.
	      for (int i = 0; i < ABUF_REGISTERS/2; ++i)
		begin
		   if (target_abuf == 0)
		     addr = ABUF0_START_ADDRESS + 4*i;
		   else
		     addr = ABUF1_START_ADDRESS + 4*i;		     
		   wdata = stream_wdata;
		   apb.write(addr, wdata, wfail);
		   stream_wdata = stream_wdata + 1;
		end
	      // 4-2.5.
	      addr = CMD_REG_ADDRESS;
	      wdata = CMD_IRQACK;
	      apb.write(addr, wdata, wfail);
	      // 4-2.6.
	      if (target_abuf == 0)
		target_abuf = 1;
	      else
		target_abuf = 0;		
	      irq_counter = irq_counter + 1;
	   end
      end : interrupt_handler

      begin : req_in_driver

	 // 4-3.1.
	 wait (play_out);
	 // 4-3.2.
	 while(play_out)
	   begin
	      repeat(10) @(posedge clk);
	      req_in = '1;
	      @(posedge clk);	      
	      req_in = '0;
	   end
	 
      end : req_in_driver


      begin: abuf_out_reader

	 stream_rdata = 1;
	 // 4-4.2.
	 forever
	   begin
	      wait(tick_out);
	      ia_streaming_test: assert ( (audio0_out == stream_rdata) && audio1_out == stream_rdata+1) else assert_error("ia_streaming_test");
	      stream_rdata = stream_rdata + 2;
	      @(posedge clk);
	   end
	 
      end: abuf_out_reader
   join_any
   disable fork;
   
   update_test_stats;      


endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task irq_out_stop_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("irq_out_stop_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task status_reg_write_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("status_reg_write_test");

   update_test_stats;

endtask
