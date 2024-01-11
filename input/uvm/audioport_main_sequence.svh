///////////////////////////////////////////////////////////
//
// audioport_main_sequence
//
///////////////////////////////////////////////////////////

class audioport_main_sequence extends audioport_main_sequence_base;   
      `uvm_object_utils(audioport_main_sequence)

   function new (string name = "");
      super.new(name);
   endfunction
   
   // ----------------------------------------------------------------------------------
   // sequence body task
   // ----------------------------------------------------------------------------------
      
   task body;
      apb_transaction write_tx;
      audioport_sequence_config seq_config;
      audio_sample_t sample;

      logic signed [31:0] input_data;
      logic [31:0] 	  level_data = 32'h80008000;
      logic [15:0] 	  level_value;
      logic [31:0] 	  cfg_data = 32'hfffffff0;
      int 		  current_abuf = 0;
      logic [4*FILTER_TAPS-1:0][31:0] filter_taps;
      logic signed [23:0] 	      audioL;
      logic signed [23:0] 	      audioR;
      uvm_event irq_event;
      irq_event = uvm_event_pool::get_global("irq_out");
      
      if (read_filter_taps(filter_taps) == 0)
	begin
	   $info("Using default filter coefficients.");
	end

      if (uvm_config_db #(audioport_sequence_config)::get(null, get_full_name(), "audioport_sequence_config", seq_config))
	begin
	   uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
	end
      else
	uvm_report_error("audioport_main_sequence.body:", "Could not get config data from uvm_config_db");
      
      write_tx = apb_transaction::type_id::create("write_tx");

      $info("Progam filter");
      
      for(int unsigned i=0; i < DSP_REGISTERS; ++i)
	begin
	   write_tx.addr = DSP_REGS_START_ADDRESS +4*i;
	   write_tx.data = filter_taps[i];
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	end


      $info("Fill ABUF");

      
      for(int unsigned i=0; i < 4*AUDIO_BUFFER_SIZE; i = i+2)
	begin
	   sample = seq_config.get_test_data();
	   write_tx.data = sample.left;
	   write_tx.addr = ABUF0_START_ADDRESS + 4*i;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   
	   start_item(write_tx);
	   finish_item(write_tx);
	   write_tx.data = sample.right;
	   write_tx.addr = ABUF0_START_ADDRESS + 4*(i+1);
	   write_tx.write_mode = '1;	      
		write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	end

      
      #2us;
      $info("Set level");
      
      write_tx.addr = LEVEL_REG_ADDRESS;
      write_tx.data = {32'h80008000};
      write_tx.write_mode = '1;	      
      write_tx.fail = 0;
      start_item(write_tx);
      finish_item(write_tx);
      
      write_tx.addr = CMD_REG_ADDRESS;
      write_tx.data = CMD_LEVEL;
      write_tx.write_mode = '1;	      
      write_tx.fail = 0;
      start_item(write_tx);
      finish_item(write_tx);
      
      #2us;      

      for(int test_counter = 1; test_counter <= 4; ++test_counter)
	begin
	   
	   case (test_counter)
	     1:
	       begin
		  $info("192kHz", test_counter);
		  write_tx.addr = CFG_REG_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000010, RATE_192000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_ADDRESS;
		  write_tx.data = CMD_CFG;
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
	       end
	     2:
	       begin
		  $info("96kHz", test_counter);		  
		  write_tx.addr = CFG_REG_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000010, RATE_96000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_ADDRESS;
		  write_tx.data = CMD_CFG;
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  		  
	       end 
	     3:
	       begin
		  $info("48kHz", test_counter);		  		  
		  write_tx.addr = CFG_REG_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000010, RATE_48000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_ADDRESS;
		  write_tx.data = CMD_CFG;
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  		  
	       end

	     4:
	       begin
		  $info("192kHz, filter=OFF, scaling", $realtime/1000.0, test_counter);		  		  		  		  
		  write_tx.addr = CFG_REG_ADDRESS;
		  write_tx.data = { 30'b00000000_00000000_00000000_000000, RATE_192000 };
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
		  write_tx.addr = CMD_REG_ADDRESS;
		  write_tx.data = CMD_CFG;
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);

		  write_tx.addr = LEVEL_REG_ADDRESS;
		  write_tx.data = {32'h40002000};
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);

		  write_tx.addr = CMD_REG_ADDRESS;
		  write_tx.data = CMD_LEVEL;
		  write_tx.write_mode = '1;	      
		  write_tx.fail = 0;
		  start_item(write_tx);
		  finish_item(write_tx);
		  
	       end
	     
	   endcase
	   

	   #2us;	   
	   $info("Start");
	   write_tx.addr = CMD_REG_ADDRESS;
	   write_tx.data = CMD_START;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);


/*	   if (test_counter == 1)
	     #2.67ms;
	   else if (test_counter == 2)
	     #5.33ms;
	   else if (test_counter == 3)
	     #10.67ms;
	   else
	     #2.67ms;
*/
	     #2.67ms;	   
	   $info("Stop");
	   write_tx.addr = CMD_REG_ADDRESS;
	   write_tx.data = CMD_STOP;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);

	   #30us;	 
	   $info("Clear");  

	   seq_config.reset();
	   current_abuf = 0;

	   write_tx.addr = CMD_REG_ADDRESS;
	   write_tx.data = CMD_CLR;
	   write_tx.write_mode = '1;	      
	   write_tx.fail = 0;
	   start_item(write_tx);
	   finish_item(write_tx);
	   
	   #10us;

	   $info("Fill ABUF");  
	   for(int unsigned i=0; i < 4*AUDIO_BUFFER_SIZE; i = i+2)
	     begin
		sample = seq_config.get_test_data();
		write_tx.addr = ABUF0_START_ADDRESS + 4*i;
		write_tx.data =  sample.left;
		write_tx.write_mode = '1;	      
		write_tx.fail = 0;
		start_item(write_tx);
		finish_item(write_tx);
		write_tx.addr = ABUF0_START_ADDRESS + 4*(i+1);
		write_tx.data = sample.right;
		write_tx.write_mode = '1;	      
		write_tx.fail = 0;
		start_item(write_tx);
		finish_item(write_tx);
	     end
	   

	   if (uvm_config_db #(audioport_sequence_config)::get(null, get_full_name(), "audioport_sequence_config", seq_config))
	     begin
		seq_config.current_abuf = 0;
		uvm_config_db #(audioport_sequence_config)::set(null, "*", "audioport_sequence_config", seq_config);
	     end
	   else
	     uvm_report_error("audioport_main_sequence.body:", "Could not get config data from uvm_config_db");
	   
	end 
      
      
      // ----To do: Add your own tests here ------------------------------------

      // ------------------------------------------------------------------------


   endtask

endclass 
