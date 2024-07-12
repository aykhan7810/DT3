`include "audioport.svh"

import audioport_pkg::*;

module control_unit 
  (
   input logic 			       clk,
   input logic 			       rst_n,
   input logic 			       PSEL,
   input logic 			       PENABLE,
   input logic 			       PWRITE,
   input logic [31:0] 		       PADDR,
   input logic [31:0] 		       PWDATA,
   input logic 			       req_in,
   output logic [31:0] 		       PRDATA,
   output logic 		       PSLVERR,
   output logic 		       PREADY,
   output logic 		       irq_out,
   output logic [31:0] 		       cfg_reg_out,
   output logic [31:0] 		       level_reg_out,
   output logic [DSP_REGISTERS*32-1:0] dsp_regs_out,
   output logic 		       cfg_out,
   output logic 		       clr_out,
   output logic 		       level_out,
   output logic 		       tick_out,
   output logic [23:0] 		       audio0_out,
   output logic [23:0] 		       audio1_out,
   output logic 		       play_out
   );

   logic [$clog2(AUDIOPORT_REGISTERS)-1:0] rindex;
   logic [$clog2(CMD_WAIT_STATES):0] 	   wctr_r;
   logic [AUDIOPORT_REGISTERS-1:0][31:0] rbank_r;
   logic 				 clr;
   logic 				 start;
   logic 				 stop;
   logic 				 clr_err;
   logic 				 cfg_err;
   logic 				 irq_err;
   logic 				 cmd_err;
   logic 				 cmd_exe;
   logic	 		   	 irqack;
   logic 				 play_r;
   logic 				 req_r;
   logic [$clog2(ABUF_REGISTERS)-1:0] rctr_r;
   logic 				 irq_r;
   
   assign PSLVERR = 0;
   
   always_comb
     begin : rindex_logic
	if (PSEL == '1) begin
	   rindex = PADDR[RINDEX_BITS+1:2];
  	end else begin
    	   rindex = '0;
  	end
     end : rindex_logic
		
	always_ff @(posedge clk or negedge rst_n) 
		begin : wctr_reg
  		if (!rst_n) 
  		begin
    		wctr_r <= '0;
  		end 
  		else begin
    	if (PSEL == '0 || PWRITE == '0) 
    	begin
      		wctr_r <= '0;
    	end 
    	else if (wctr_r == '0) 
    	begin
      		if (PSEL && !PENABLE && PWRITE && PADDR == CMD_REG_ADDRESS) begin
        	wctr_r <= 1;
      		end 
      		else begin
        	wctr_r <= 0;
      		end
    	end 
    	else if (wctr_r < CMD_WAIT_STATES) begin
      	wctr_r <= wctr_r + 1;
    	end 
    	else if (wctr_r == CMD_WAIT_STATES) begin
      	wctr_r <= 0;
    	end
  		end
		end : wctr_reg
		
	always_comb
	  begin : PREADY_output
	     if (wctr_r == 0)
	       PREADY = '1;
	     else
	       PREADY = '0;
	  end : PREADY_output


  always_ff @(posedge clk or negedge rst_n) 
  begin: rbank_r_reg
    if (!rst_n) begin
      rbank_r <= '0;
    end else begin
      // register_bank
      if (PSEL && PENABLE && PWRITE && (wctr_r == 0)) begin
        rbank_r[rindex] <= PWDATA;
      end
      
      // cmd_clr
      if (clr) begin
        rbank_r <= '0;
      end

      if (start) begin		//play_status
        rbank_r[STATUS_REG_INDEX][STATUS_PLAY] <= '1;
      end
      if (stop) begin 		//standby_status
        rbank_r[STATUS_REG_INDEX][STATUS_PLAY] <= '0;
      end
      if (clr_err) begin	//clr_err
        rbank_r[STATUS_REG_INDEX][STATUS_CLR_ERR] <= '1;
      end
      if (cfg_err) begin	//cfg_err
        rbank_r[STATUS_REG_INDEX][STATUS_CFG_ERR] <= '1;
      end
      if (irq_err && (PADDR != STATUS_REG_ADDRESS)) begin	//irq_err && status_reg_write
        rbank_r[STATUS_REG_INDEX][STATUS_IRQ_ERR] <= '1;
      end
      if (cmd_err) begin	//cmd_err
        rbank_r[STATUS_REG_INDEX][STATUS_CMD_ERR] <= '1;
      end   
    end
  end : rbank_r_reg
  
  always_comb 
  begin : PRDATA_logic
    if (PSEL)
      PRDATA = rbank_r[rindex];
    else
      PRDATA = '0;
  end : PRDATA_logic
  
  assign cfg_reg_out = rbank_r[CFG_REG_INDEX];
  
  assign level_reg_out = rbank_r[LEVEL_REG_INDEX];
  
  assign dsp_regs_out = rbank_r[DSP_REGS_END_INDEX:DSP_REGS_START_INDEX];
  
  always_comb
  begin : cmd_exe_logic
  	if (PSEL && PENABLE && PWRITE && (wctr_r == 0) && (rindex == CMD_REG_INDEX)) 		begin
      cmd_exe = 1'b1;
    end else begin
      cmd_exe = 1'b0;
    end
  end: cmd_exe_logic
  
  always_comb
  begin: cmd_err_logic
  	if (cmd_exe) begin
    case (PWDATA)
      CMD_START,
      CMD_STOP,
      CMD_CLR,
      CMD_IRQACK,
      CMD_CFG,
      CMD_LEVEL: cmd_err = 1'b0;
      default: cmd_err = 1'b1;
    endcase
  	end else begin
    cmd_err = 1'b0;
  end
  end: cmd_err_logic
  
  always_comb
  begin : start_logic
  	if (cmd_exe && PWDATA == CMD_START) begin
  		start = '1;
  	end else begin
  		start = '0;
  	end  	
  end : start_logic
  
  always_comb
  begin : stop_logic
  	if (cmd_exe && PWDATA == CMD_STOP) begin
  		stop = '1;
  	end else begin
  		stop = '0;
  	end  	
  end : stop_logic
  
  always_comb
  begin : level_out_logic
  	if (cmd_exe && PWDATA == CMD_LEVEL) begin
  		level_out = '1;
  	end else begin
  		level_out = '0;
  	end  	
  end : level_out_logic
  
  always_comb
  begin : irq_ack_logic
  	if (cmd_exe && PWDATA == CMD_IRQACK) begin
  		irqack = '1;
  	end else begin
  		irqack = '0;
  	end  	
  end : irq_ack_logic
  
  always_ff @(posedge clk or negedge rst_n) 
  begin : play_r_reg
    if (!rst_n) begin
      play_r <= 1'b0;
    end else begin
      if (start) begin
        play_r <= 1'b1;
      end else if (stop) begin
        play_r <= 1'b0;
      end
    end
  end : play_r_reg
  
  assign play_out = play_r;
  
  always_comb
  begin : clr_logic
  	if (!play_r && cmd_exe && PWDATA == CMD_CLR) begin
  		clr = '1;
  	end else begin
  		clr = '0;
  	end  	
  end : clr_logic
  
  assign clr_out = clr;
  
  always_comb
  begin : clr_err_logic
  	if (play_r && cmd_exe && PWDATA == CMD_CLR) begin
  		clr_err = '1;
  	end else begin
  		clr_err = '0;
  	end  	
  end : clr_err_logic
  
  always_comb
  begin : cfg_out_logic
  	if (!play_r && cmd_exe && PWDATA == CMD_CFG) begin
  		cfg_out = '1;
  	end else begin
  		cfg_out = '0;
  	end  	
  end : cfg_out_logic
  
  always_comb
  begin : cfg_err_logic
  	if (play_r && cmd_exe && PWDATA == CMD_CFG) begin
  		cfg_err = '1;
  	end else begin
  		cfg_err = '0;
  	end  	
  end : cfg_err_logic
  
  always_ff @(posedge clk or negedge rst_n) 
  begin : req_r_reg
    if (!rst_n) begin
      req_r <= 1'b0;
    end else begin
      if (play_r) begin
        req_r <= req_in;
      end else begin
        req_r <= '0;
      end
    end
  end : req_r_reg
  
  always_comb
  begin : tick_out_logic
  	if (!play_r) 
  	begin : abuf_standby
  		tick_out = '1;
  	end : abuf_standby 
  	else 
  	begin : abuf_tick
  		tick_out = '0;
  	end : abuf_tick  	
  end : tick_out_logic
  
  always_ff @(posedge clk or negedge rst_n) 
  begin : rctr_r_reg
    if (!rst_n)
      rctr_r <= '0;
    else begin
      if (play_r == 1'b0) begin
        rctr_r <= '0;
      end else if (stop == 1'b1) begin
        rctr_r <= '0;
      	end else if (play_r == 1'b1 && stop == 1'b0 && req_r == 1'b1) begin
        	if (rctr_r < ABUF_REGISTERS - 2) begin
          	rctr_r <= rctr_r + 2;
        	end 
      	end
      end
   end : rctr_r_reg
   
   always_ff @(posedge clk or negedge rst_n) 
   begin : irq_r_reg
    if (!rst_n) begin
      irq_r <= 1'b0;
    end else begin
      if (play_r == 1'b1 && req_r == 1'b1 && stop == 1'b0 && irqack == 1'b0 && (rctr_r == ABUF0_END_INDEX-1 || rctr_r == ABUF1_END_INDEX-1)) begin
        irq_r <= 1'b1;
      end else if (stop == 1'b1 || irqack == 1'b1) begin
        irq_r <= 1'b0;
      end
    end
  	end : irq_r_reg
  	
  	assign irq_out = irq_r;
  	
  	always_comb
  	begin : irq_err_logic
  	if (irq_r && req_r && play_r && !stop && !irqack && (rctr_r == ABUF0_END_INDEX-1 || rctr_r == ABUF1_END_INDEX-1)) begin
  		irq_err = '1;
  	end else 
  		irq_err = '0;	
  	end : irq_err_logic
  	
  	always_comb
  	begin : audio0_out_logic
  	audio0_out = rbank_r[rctr_r + ABUF0_START_INDEX][23:0];
  	end: audio0_out_logic
  	
  	always_comb
  	begin : audio1_out_logic
  	audio1_out = rbank_r[rctr_r + ABUF0_START_INDEX + 1][23:0];
  	end: audio1_out_logic
   
endmodule
