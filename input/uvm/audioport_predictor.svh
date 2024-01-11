///////////////////////////////////////////////////////////
//
// audioport_predictor
//
// This component implements a reference mode for the
// audioport. It receives APB transactions from the apb_monitor
// through an analysis export,  and transmits responses to the 
// audioport_comparator through a get export.
//
///////////////////////////////////////////////////////////

class audioport_predictor extends uvm_component;
   `uvm_component_utils(audioport_predictor)
   
   uvm_analysis_imp #(apb_transaction, audioport_predictor) apb_analysis_export;
   uvm_nonblocking_get_imp #(i2s_transaction, audioport_predictor) predictor_get_export;

   // ----------------------------------------------------------------------------------
   // Registers
   // ----------------------------------------------------------------------------------

   logic [31:0] 		    cmd_r = '0;
   logic [31:0] 		    status_r = '0;   
   logic [31:0] 		    level_r = '0;      
   logic [31:0] 		    cfg_r = '0;
   logic [DSP_REGISTERS-1:0][31:0]  dsp_regs_r = '0;   
   logic [ABUF_REGISTERS-1:0][23:0] abuf_r;
   int 				    rctr_r = 0;
   logic 			    play_mode = '0;
   
   // ----------------------------------------------------------------------------------
   // filter coefficients
   // ----------------------------------------------------------------------------------
   
   logic signed [DSP_REGISTERS-1:0][31:0] active_dsp_regs = '0;

   // ----------------------------------------------------------------------------------
   // scaler levels
   // ----------------------------------------------------------------------------------
   
   logic [1:0][15:0] active_level_data = '0;

   // ----------------------------------------------------------------------------------
   // config register(s) loaded with CONFIG command
   // ----------------------------------------------------------------------------------
   
   logic [31:0] active_config_data = '0;            

   // ----------------------------------------------------------------------------------
   // dsp_unit filter and output registers
   // ----------------------------------------------------------------------------------

   logic signed [23:0] audio0;
   logic signed [23:0] audio1;   
   logic signed [1:0][23:0] filter_outputs;
   logic signed [23:0] 	    dsp0;
   logic signed [23:0] 	    dsp1;   
   
   
   logic signed [FILTER_TAPS-1:0][1:0][23:0] filter_data = '0;
   logic [1:0][23:0] 		  audio_outputs = '0;

   // ----------------------------------------------------------------------------------
   // Predictor output queue
   // ----------------------------------------------------------------------------------
   
   i2s_transaction output_queue[$];
   int delete_queue_on_start = 0;
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      apb_analysis_export = new("apb_analysis_export", this);      
      predictor_get_export = new("predictor_get_port", this);
   endfunction

   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      play_mode = '0;
    endfunction

   // ----------------------------------------------------------------------------------
   // write method for the analysis export.
   // ----------------------------------------------------------------------------------
   
   function void write(apb_transaction t);
      apb_transaction tx = t;
      
      if (t.write_mode == '1)
	begin
	   if (tx.addr == CMD_REG_ADDRESS)
	     begin
`ifdef DEBUG
		$display("%f: audioport_predictor: CMD_REG = %h", $realtime, tx.data);
`endif
		cmd_r = tx.data;
		case (cmd_r)
		  CMD_START:
		    begin
		       i2s_transaction i2s_tx = new();      
		       play_mode = '1;
		       if (delete_queue_on_start) output_queue.delete();
		       delete_queue_on_start = 0;
		       i2s_tx.audio_data[0] = 0;
		       i2s_tx.audio_data[1] = 0;
		       output_queue.push_back(i2s_tx);
		       do_dsp();
		       
		       
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_START -------------------------------------------------------------------------------", $realtime);
`endif
		    end
		  CMD_STOP:
		    begin
		       play_mode = '0;	
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_STOP -------------------------------.------------------------------------------------", $realtime);
`endif
		    end
		  CMD_CFG:
		    begin
		       do_configs();	
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_CFG -------------------------------.------------------------------------------------", $realtime);
`endif
		    end
		  CMD_LEVEL:
		    begin
		    set_levels(level_r);
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_LEVEL -------------------------------.------------------------------------------------", $realtime);
`endif
		    end
		  CMD_CLR:
		    begin
		       do_clear();
		       delete_queue_on_start = 1;		       
`ifdef DEBUG
		       $display("%f: audioport_predictor CMD_CLR ---------------------------------------------------------------------------------", $realtime);
`endif
		    end
		endcase
		
	     end
	   else if (tx.addr == STATUS_REG_ADDRESS)
	     begin
		status_r = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: STATUS_REG = %h", $realtime, tx.data);		
`endif
	     end
	   else if (tx.addr == LEVEL_REG_ADDRESS)
	     begin
		level_r = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: LEVEL_REG = %h", $realtime, tx.data);		
`endif
	     end
	   else if (tx.addr == CFG_REG_ADDRESS)
	     begin
		cfg_r = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: CFG_REG = %h", $realtime, tx.data);		
`endif
	     end
	   else if (tx.addr >= DSP_REGS_START_ADDRESS && tx.addr <= DSP_REGS_END_ADDRESS)
	     begin
		int rindex = (tx.addr - DSP_REGS_START_ADDRESS)/4;
		dsp_regs_r[rindex] = tx.data;
`ifdef DEBUG
		$display("%f: audioport_predictor: dsp_regs_r[%d] = %h", $realtime, rindex, dsp_regs_r[rindex]);				
`endif
	     end
	   else if (tx.addr >= ABUF0_START_ADDRESS && tx.addr <= ABUF1_END_ADDRESS)
	     begin
		int rindex = (tx.addr - ABUF0_START_ADDRESS)/4;		
		abuf_r[rindex] = tx.data[23:0];
`ifdef DEBUG
		$display("%f: audioport_predictor: abuf_r[%d] = %d", $realtime, rindex, $signed(abuf_r[rindex]));						
`endif
	     end
	   else
	     begin
`ifdef DEBUG
		$display("%f: audioport_predictor: Out-of-band address %h", $realtime, tx.addr);						
`endif
	     end
	end
   endfunction

   // ----------------------------------------------------------------------------------
   // can_get method tells if data are available
   // ----------------------------------------------------------------------------------
   
   function bit can_get();
      return 1;
   endfunction

   // ----------------------------------------------------------------------------------
   // try_get method that allows audioport_comparator to get next reference value
   // ----------------------------------------------------------------------------------
   
   function int try_get(output i2s_transaction t);
      t = output_queue.pop_front();
      do_dsp();

      
`ifdef DEBUG
      $display("%f: audioport_predictor: queue_size = %d", $realtime, output_queue.size());
`endif
`ifdef DEBUG
      $display("%f: audioport_predictor: audio out = %d, %d", $realtime, $signed(t.audio_data[0]), $signed(t.audio_data[1]));
`endif
      
      return 1;
   endfunction
 

   // ----------------------------------------------------------------------------------
   // Method for executing CMD_CFG: copy from input variables to 'active' variables
   // ----------------------------------------------------------------------------------
   
   function void do_configs();
      active_config_data = cfg_r;
      for (int i=0; i < DSP_REGISTERS; ++i)
	begin
	   active_dsp_regs[i] = dsp_regs_r[i];
	end
   endfunction

   // ----------------------------------------------------------------------------------
   // Method for executing CMD_CLR: reset variables
   // ----------------------------------------------------------------------------------

   function void do_clear();
      for(int j=0; j < ABUF_REGISTERS; ++j)
	begin
	   abuf_r[j] = '0;
	end
      
      for(int j=0; j < FILTER_TAPS; ++j)
	begin
	   filter_data[j][0] = '0;
	   filter_data[j][1] = '0;		
	end
      rctr_r = 0;
      audio0 = '0;
      audio1 = '0;
      dsp0 = '0;
      dsp1 = '0;
      audio_outputs[0] = '0;
      audio_outputs[1] = '0;
   endfunction

   // ----------------------------------------------------------------------------------
   // do_dsp: Helper method for executing 'dsp_unit'
   // ----------------------------------------------------------------------------------

   function void do_dsp();

      logic signed [23:0] d;
      logic signed [31:0] c;      
      logic signed [32+24+FILTER_TAPS-1:0] accu30L, accu330L, accu30R, accu330R;
      logic signed [32+24+FILTER_TAPS:0] sumL, sumR;	   
      logic signed [16:0] 		levelL = active_level_data[0];
      logic signed [16:0] 		levelR = active_level_data[1];		
      logic signed [41:0] 		scaledL;
      logic signed [41:0] 		scaledR;
      logic signed [42:0] 		scaledLR;

      i2s_transaction i2s_tx = new();      

`ifdef DEBUG
      $display("%f: audioport_predictor: abuf read counter = %d", $realtime, rctr_r);
`endif
      audio0 = abuf_r[rctr_r];
      rctr_r = rctr_r + 1;
      audio1 = abuf_r[rctr_r];
      rctr_r = rctr_r + 1;
      if (rctr_r >= 4*AUDIO_BUFFER_SIZE-1)
	rctr_r = 0;
      
      // Filter
`ifdef DEBUG
      $display("%f: audioport_predictor: abuf_out = %d %d", $realtime, $signed(audio0), $signed(audio1));	   
`endif      
      if (active_config_data[CFG_FILTER] == '1)
	begin
	   for (int tap=FILTER_TAPS-1; tap > 0; --tap)
	     begin
		filter_data[tap][0] = filter_data[tap-1][0];
		filter_data[tap][1] = filter_data[tap-1][1];			  
	     end
	   filter_data[0][0] = audio0;
	   filter_data[0][1] = audio1;
	   
	   accu30L = 0;
	   accu330L = 0;
	   accu30R = 0;
	   accu330R = 0;

	   for (int tap=0; tap < FILTER_TAPS; ++tap)
	     begin
		logic signed [32+24-1:0] mul;
		d = filter_data[tap][0];
		c = active_dsp_regs[tap];
		mul = c * d;
		accu30L = accu30L + mul;
		d = filter_data[tap][1];
		c = active_dsp_regs[FILTER_TAPS+tap];
		mul = c * d;
		accu30R = accu30R + mul;
		d = filter_data[tap][0];
		c = active_dsp_regs[2*FILTER_TAPS+tap];
		mul = c * d;
		accu330L = accu330L + mul;
		d = filter_data[tap][1];
		c = active_dsp_regs[3*FILTER_TAPS+tap];
		mul = c * d;
		accu330R = accu330R + mul;
	     end 
	   
	   sumL = accu30L + accu330R;
	   sumR = accu30R + accu330L;
	   sumL = (sumL >>> 32);
	   sumR = (sumR >>> 32);	   
	   filter_outputs[0] = sumL;
	   filter_outputs[1] = sumR;
	end
      else
	begin
	   filter_outputs[0] = audio0;
	   filter_outputs[1] = audio1;
	end
`ifdef DEBUG
      $display("%f: audioport_predictor: scaler in = %d %d", $realtime, $signed(filter_outputs[0]), $signed(filter_outputs[1]));
`endif      
      // scaler
      
      scaledL = signed'(filter_outputs[0]);
      scaledR = signed'(filter_outputs[1]);
      levelL = '0;
      levelR = '0;
      levelL[15:0] = active_level_data[0];
      levelR[15:0] = active_level_data[1];
      
      scaledL = scaledL * levelL;
      scaledR = scaledR * levelR;		
      scaledL = scaledL >>> 15;
      scaledR = scaledR >>> 15;		
      
      if (active_config_data[CFG_MONO] == '0)
	begin
	   dsp0 = scaledL;
	   dsp1 = scaledR;
	end
      else
	begin
	   scaledLR = (scaledL + scaledR);
	   scaledLR = scaledLR >>> 1;
	   dsp0 = scaledLR;
	   dsp1 = scaledLR;
	end
`ifdef DEBUG
      $display("%f: audioport_predictor dsp_unit out = %d %d", $realtime, $signed(dsp0), $signed(dsp1));      
`endif
      audio_outputs[0] = dsp0;
      audio_outputs[1] = dsp1;	         

      i2s_tx.audio_data[0] = audio_outputs[0];
      i2s_tx.audio_data[1] = audio_outputs[1];	   
      output_queue.push_back(i2s_tx);
      
endfunction

   // ----------------------------------------------------------------------------------
   // set_levels: Method for setting levels from level register
   // ----------------------------------------------------------------------------------
   
   function void set_levels(logic [31:0] level_setting);
 	   active_level_data[0] = level_setting[15:0];
	   active_level_data[1] = level_setting[31:16];		
   endfunction


endclass
