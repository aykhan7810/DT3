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
   
   // 1. Set req_in to zero
   req_in = '0;

   // 2. Execute read access to all valid register addresses
   for (addr = AUDIOPORT_START_ADDRESS; addr <= AUDIOPORT_END_ADDRESS; addr += 4) 
   begin
      rfail = '0;
      apb.read(addr, rdata, rfail);
      assert(!rfail) else $fatal("Read failed at valid address %h", addr);

      // Whitebox assertion placeholder(to be developed on week 3)
   end

   // 3. Execute a read access to an address outside the audioport range
   rfail = '0;
   invalid_addr = AUDIOPORT_END_ADDRESS + 4;
   apb.read(invalid_addr, rdata, rfail);
   //assert(rfail) else $fatal("Read did not fail at invalid address %h", invalid_addr);

   // Whitebox assertion placeholder (to be developed on week 3)

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task wait_states_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("wait_states_test");

   // 1. Set APB ports and req_in to zero
   req_in = '0;
   addr = '0;
   wdata = '0;
   rdata = '0;
   wfail = '0;
   rfail = '0;

   // 2. Write command code CMD_STOP to register CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_STOP;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS %h", addr);

   // assertion placeholder (to be developed on week 3)

   // 3. Read data from CMD_REG_ADDRESS
   apb.read(addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at CMD_REG_ADDRESS %h", addr);

   // Concurrent assertion placeholder (to be developed on week 3)

   // 4. Write data to CFG_REG_ADDRESS
   addr = CFG_REG_ADDRESS;
   wdata = $urandom;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CFG_REG_ADDRESS %h", addr);

   // Concurrent assertion placeholder (to be developed on week 3)

   // 5. Read data from CFG_REG_ADDRESS
   apb.read(addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at CFG_REG_ADDRESS %h", addr);

   // Concurrent assertion placeholder (to be developed on week 3);

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task register_bank_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("register_bank_test");

   // 1. Set APB ports and req_in to zero
   req_in = '0;
   addr = '0;
   wdata = '0;
   rdata = '0;
   wfail = '0;
   rfail = '0;

   // 2. Write random non-zero data to all valid register addresses and read back to compare
   for (addr = AUDIOPORT_START_ADDRESS; addr <= AUDIOPORT_END_ADDRESS; addr += 4) begin
      wdata = $urandom | 32'h1; // Ensuring non-zero data
      wfail = '0;
      rfail = '0;
      
      apb.write(addr, wdata, wfail);
      assert(!wfail) else $fatal("Write failed at address %h", addr);

      apb.read(addr, rdata, rfail);
      assert(!rfail) else $fatal("Read failed at address %h", addr);

      ia_reg_test: assert(wdata == rdata) else $fatal("Mismatch at address %h: wrote %h, read %h", addr, wdata, rdata);
   end

   // 3. Execute a read access to an address outside the audioport range and check PRDATA == 0
   invalid_addr = AUDIOPORT_END_ADDRESS + 4;
   rfail = '0;
   apb.read(invalid_addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at invalid address %h", invalid_addr);

   // assertion placeholder (to be developed on week 3;

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_exe_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_exe_test");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_start_stop_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_start_stop_test");

   // 1. Set APB ports and req_in to zero and execute a reset
   req_in = '0;
   addr = '0;
   wdata = '0;
   rdata = '0;
   wfail = '0;
   rfail = '0;

   reset_test;

   // 2. Write code CMD_START to CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_START;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_START");

   // 3. Read from STATUS_REG_ADDRESS and check state of STATUS_PLAY bit
   addr = STATUS_REG_ADDRESS;
   apb.read(addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at STATUS_REG_ADDRESS after CMD_START");
   ia_start_status_test: assert((rdata & STATUS_PLAY) == STATUS_PLAY) else $fatal("STATUS_PLAY bit is not set after CMD_START");

   // 4. Write code CMD_STOP into the CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_STOP;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_STOP");

   // 5. Read STATUS_REG_ADDRESS and check state of STATUS_PLAY bit
   addr = STATUS_REG_ADDRESS;
   apb.read(addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at STATUS_REG_ADDRESS after CMD_STOP");
   ia_stop_status_test: assert((rdata & STATUS_PLAY) == 0) else $fatal("STATUS_PLAY bit is not cleared after CMD_STOP");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_level_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_level_test");
   
   // 1. Set APB ports and req_in to zero
   req_in = '0;
   addr = '0;
   wdata = '0;
   wfail = '0;

   // 2. Write the command code CMD_LEVEL to CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_LEVEL;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_LEVEL");

   // assertion placeholder (to be developed in week 3;

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_clr_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_clr_test");
   
   // 1. Set APB ports and req_in to zero and execute a reset
   req_in = '0;
   addr = '0;
   wdata = '0;
   rdata = '0;
   wfail = '0;
   rfail = '0;

   reset_test;

   // 2. Write 32'hffffffff (all ones) to all valid register addresses in the range ABUF0_START_ADDRESS - ABUF1_END_ADDRESS
   for (addr = ABUF0_START_ADDRESS; addr <= ABUF1_END_ADDRESS; addr += 4) begin
      wdata = 32'hffffffff;
      apb.write(addr, wdata, wfail);
      assert(!wfail) else $fatal("Write failed at address %h", addr);
   end

   // 3. Write the command code CMD_CLR into CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_CLR;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_CLR");

   // assertion placeholder for clr_out response;

   // 4. Read from all valid register addresses in the range ABUF0_START_ADDRESS - ABUF1_END_ADDRESS
   for (addr = ABUF0_START_ADDRESS; addr <= ABUF1_END_ADDRESS; addr += 4) begin
      apb.read(addr, rdata, rfail);
      assert(!rfail) else $fatal("Read failed at address %h", addr);
      ia_cmd_clr_test: assert(rdata == 0) else $fatal("Clear test failed at address %h, read value: %h", addr, rdata);
   end

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cmd_cfg_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cmd_cfg_test");
   
   // 1. Set APB ports and req_in to zero
   req_in = '0;
   addr = '0;
   wdata = '0;
   wfail = '0;

   // Execute Reset
   reset_test;

   // 2. Write the command code CMD_CFG into CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_CFG;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_CFG");

   // Blackbox assertion placeholder (to be developed in week 3)

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task clr_err_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("clr_err_test");
   
   // 1. Set APB ports and req_in to zero and execute a reset
   req_in = '0;
   addr = '0;
   wdata = '0;
   rdata = '0;
   wfail = '0;
   rfail = '0;

   reset_test;

   // 2. Write 32'hffffffff (all ones) to all registers in the ABUF region
   for (addr = ABUF0_START_ADDRESS; addr <= ABUF1_END_ADDRESS; addr += 4) begin
      wdata = 32'hffffffff;
      apb.write(addr, wdata, wfail);
      assert(!wfail) else $fatal("Write failed at address %h", addr);
   end

   // 3. Write 32'h00000000 into STATUS_REG_ADDRESS to clear all status bits
   addr = STATUS_REG_ADDRESS;
   wdata = 32'h00000000;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at STATUS_REG_ADDRESS with 0");

   // 4. Write the command code CMD_START into CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_START;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_START");

   // 5. Write the command code CMD_CLR into the CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_CLR;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_CLR");

   // 6. Read all registers in the ABUF region and check that all bits are set to '1
   for (addr = ABUF0_START_ADDRESS; addr <= ABUF1_END_ADDRESS; addr += 4) begin
      apb.read(addr, rdata, rfail);
      assert(!rfail) else $fatal("Read failed at address %h", addr);
      ia_clr_err_test_data: assert(rdata == 32'hffffffff) else $fatal("Clear error test failed at address %h, read value: %h", addr, rdata);
   end

   // 7. Read from STATUS_REG_ADDRESS and check that the state of STATUS_CLR_ERR bit is '1
   addr = STATUS_REG_ADDRESS;
   apb.read(addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at STATUS_REG_ADDRESS");
   ia_clr_err_test_status: assert((rdata & STATUS_CLR_ERR) == STATUS_CLR_ERR) else $fatal("STATUS_CLR_ERR bit is not set");

   update_test_stats;

endtask

////////////////////////////////////////////////////////////////////////////////////////////////////
task cfg_err_test;
////////////////////////////////////////////////////////////////////////////////////////////////////

   $info("cfg_err_test");
   
   // 1. Set APB ports and req_in to zero and execute a reset
   req_in = '0;
   addr = '0;
   wdata = '0;
   rdata = '0;
   wfail = '0;
   rfail = '0;

   reset_test;

   // 2. Write 32'h00000000 into STATUS_REG_ADDRESS to clear all status bits
   addr = STATUS_REG_ADDRESS;
   wdata = 32'h00000000;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at STATUS_REG_ADDRESS with 0");

   // 3. Write the command code CMD_START into CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_START;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_START");

   // 4. Write the command code CMD_CFG into CMD_REG_ADDRESS
   addr = CMD_REG_ADDRESS;
   wdata = CMD_CFG;
   apb.write(addr, wdata, wfail);
   assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_CFG");

   // 5. Read from STATUS_REG_ADDRESS and check that the state of STATUS_CFG_ERR bit is '1
   addr = STATUS_REG_ADDRESS;
   apb.read(addr, rdata, rfail);
   assert(!rfail) else $fatal("Read failed at STATUS_REG_ADDRESS");
   ia_cfg_err_test: assert((rdata & STATUS_CFG_ERR) != 0) else assert_error("STATUS_CFG_ERR bit is not set"); //$warning("STATUS_CFG_ERR bit is not set");

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
   
   // 1. Set APB ports and req_in to zero
   req_in = '0;
   addr = '0;
   wdata = '0;
   wfail = '0;
   rfail = '0;

   // Execute reset
   reset_test;

   // Fork two concurrent processes
   fork
      begin : apb_control
         // 2-1.1 Write the command code CMD_START into the CMD_REG_ADDRESS
         addr = CMD_REG_ADDRESS;
         wdata = CMD_START;
         apb.write(addr, wdata, wfail);
         assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_START");

         // Repeating steps 2-1.2 - 2-1.3, 5 times
         repeat (5) begin
            // 2-1.2 Set irq_out state to 0 and monitor irq_out_state
            irq_out_state = 0;
            while (!irq_out_state) begin
               irq.monitor(irq_out_state);
            end

            // 2-1.3 Write the command code CMD_IRQACK into CMD_REG_ADDRESS when irq_out rises
            addr = CMD_REG_ADDRESS;
            wdata = CMD_IRQACK;
            apb.write(addr, wdata, wfail);
            assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_IRQACK");

            // Response to be checked with blackbox assertions
         end

         // 2-1.4 Write the command code CMD_STOP into the CMD_REG_ADDRESS
         addr = CMD_REG_ADDRESS;
         wdata = CMD_STOP;
         apb.write(addr, wdata, wfail);
         assert(!wfail) else $fatal("Write failed at CMD_REG_ADDRESS with CMD_STOP");
      end : apb_control

      begin : req_writer
         // 2-2.1 Wait until play_out rises
         wait (play_out);

         // 2-2.2 Generate a one-clock-cycle-long req_in pulse every 10 clock cycles
         forever begin
            repeat (10) @(posedge clk);
            req_in = '1;
            @(posedge clk);
            req_in = '0;
         end
      end : req_writer
   join_any
   disable fork; // End processes when one exits

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
