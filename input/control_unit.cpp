#include "control_unit.h"

#ifdef control_unit_as_rtl

void control_unit::control_regs_proc()
{

  if (rst_n.read() == 0)
    {
      wctr_r = 0;
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	rbank_r[i] = 0;
      irq_r = 0;
      play_r = 0;
      rctr_r = 0;
      req_r = 0;
    }
  else
    {
      wctr_r = wctr_ns;
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	rbank_r[i] =  rbank_ns[i];
      irq_r = irq_ns;
      play_r = play_ns;
      rctr_r = rctr_ns;
      req_r = req_ns;
    }
}

#define use_sc_signals

#ifdef use_sc_signals

void control_unit::control_logic_proc()
{

  // Internal address decoding
  if(PSEL == 1)
    rindex = (PADDR.read() - AUDIOPORT_START_ADDRESS) >> 2;
  else
    rindex = 0;
  
  // PRDATA mux
  if (PSEL)
    PRDATA = rbank_r[rindex.read()];
  else
    PRDATA = 0;
  
  // write decoder
  write = 0;
  cmd_exe = 0;
  if (wctr_r.read() == 0 && PSEL && PENABLE == 1 && PWRITE == 1)
    { 
      write = 1;
      if (rindex.read() == CMD_REG_INDEX)
	cmd_exe = 1;
    }
  
  // PREADY decoder
  if (wctr_r.read() == 0)
    PREADY = 1;
  else
    PREADY = 0;
  
  // PSLVERR
  PSLVERR = 0;
  
  // Command decoding
  start = 0;
  stop = 0;
  clr = 0;
  irqack = 0;
  cmd_err = 0;
  clr_err = 0;
  cfg_out = 0;
  cfg_err = 0;
  irq_err = 0;
  level_out = 0;	
  
  if (cmd_exe.read())
    {
      sc_uint<32> pwdata = PWDATA;
      switch (pwdata)
	{
	case CMD_NOP:
	  break;
	case CMD_CLR:   
	  if (!play_r)
	    clr = 1;
	  else
	    clr_err = 1;
	  break;
	case CMD_CFG:   
	  if (!play_r)
	    cfg_out = 1;	  
	  else
	    cfg_err = 1;
	  break;
	case CMD_LEVEL: 
	  level_out = 1;
	  break;
	case CMD_START: 
	  start = 1;
	  break;
	case CMD_STOP:  
	  stop = 1;
	  break;
	case CMD_IRQACK:  
	  irqack = 1;
	  break;
	default:
	  cmd_err = 1;
	  break;
	}
    }
  
  // wait counter
  wctr_ns = wctr_r;
  if (wctr_r.read() == 0)
    {
      if (PSEL && !PENABLE && PWRITE && rindex.read() == CMD_REG_INDEX)	  
	wctr_ns = 1;
    }
  else if (wctr_r.read() < CMD_WAIT_STATES)
    wctr_ns = wctr_r.read() + 1;
  else
    wctr_ns = 0;

  // irq next state
  if (!(play_r.read()) || stop)
    irq_ns = 0; 
  else if (irqack)
    irq_ns = 0;	       
  else if (play_r.read() && req_r == 1 && ( ((ABUF0_START_INDEX + rctr_r.read()) == ABUF0_END_INDEX-1)  || 
					     ((ABUF0_START_INDEX + rctr_r.read()) == ABUF1_END_INDEX-1)))
    {
      if (irq_r)
	{
	  irq_ns = 1;
	  irq_err = 1;
	}
      else
	{
	  irq_ns = 1;
	  irq_err = 0;
	}
    }
  else
    irq_ns = irq_r;

  // Outputs
  clr_out = clr;
  irq_out = irq_r;
  play_out = play_r;
  
  if (play_r)
    tick_out = req_r;
  else
    tick_out = 0;

  sc_bv<DSP_REGISTERS*32>  dsp_regs;  
  for(int i=0; i < DSP_REGISTERS; ++i)
    dsp_regs.range((i+1)*32-1, i*32) = (sc_bv<32>)(rbank_ns[DSP_REGS_START_INDEX+i]);
  dsp_regs_out = dsp_regs;

  cfg_reg_out = rbank_r[CFG_REG_INDEX];
  level_reg_out = rbank_r[LEVEL_REG_INDEX];
	
  audio0_out = (sc_int<24>) (rbank_r[ABUF0_START_INDEX + rctr_r.read()   ].read());
  audio1_out = (sc_int<24>) (rbank_r[ABUF0_START_INDEX + rctr_r.read() +1].read());	
    

  // Register bank control
  for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
    rbank_ns[i] = rbank_r[i];

  if (clr)
    {
      for (int i = ABUF0_START_INDEX; i <= ABUF1_END_INDEX; ++i)
	rbank_ns[i] = 0;
    }

  if (write)
    rbank_ns[rindex.read()].write(PWDATA);
  
  if (cmd_err || clr_err || cfg_err || irq_err || start || stop)
    {
      sc_uint<32> tmp = rbank_r[STATUS_REG_INDEX].read();
      if (cmd_err)
	tmp[STATUS_CMD_ERR] = 1;      
      if (clr_err)
	tmp[STATUS_CLR_ERR] = 1;      
      if (cfg_err)
	tmp[STATUS_CFG_ERR] = 1;      
      if (irq_err && !(write && rindex.read() == STATUS_REG_INDEX) )
	tmp[STATUS_IRQ_ERR] = 1;      
      if (start)
	tmp[STATUS_PLAY] = 1;      
      else if (stop)
	tmp[STATUS_PLAY] = 0;      
      rbank_ns[STATUS_REG_INDEX].write(tmp);
    }
  
  // Play mode control
  if (start == 1)
    play_ns = 1;
  else if (stop == 1)
    play_ns = 0;		      
  else
    play_ns = play_r;

  // Read counter control  
  rctr_ns = rctr_r;    
  if (clr == 1)
    rctr_ns = 0;	     
  else if (req_r == 1)
    {
      if (rctr_r.read() < 4*AUDIO_BUFFER_SIZE-2)
	rctr_ns = rctr_r.read() + 2;
      else
	rctr_ns = 0;
    }
  
  // tick register
  if (play_r.read() && req_in)
    req_ns = 1;
  else
    req_ns = 0;
}


#else

void control_unit::control_logic_proc()
{

  // Internal address decoding
  if(PSEL == 1)
    rindex = (PADDR.read() - AUDIOPORT_START_ADDRESS) >> 2;
  else
    rindex = 0;
  
  // PRDATA mux
  if (PSEL)
    PRDATA = rbank_r[rindex];
  else
    PRDATA = 0;
  
  // write decoder
  write = 0;
  cmd_exe = 0;
  if (wctr_r.read() == 0 && PSEL && PENABLE == 1 && PWRITE == 1)
    { 
      write = 1;
      if (rindex == CMD_REG_INDEX)
	cmd_exe = 1;
    }
  
  // PREADY decoder
  if (wctr_r.read() == 0)
    PREADY = 1;
  else
    PREADY = 0;
  
  // PSLVERR
  PSLVERR = 0;
  
  // Command decoding
  start = 0;
  stop = 0;
  clr = 0;
  irqack = 0;
  cmd_err = 0;
  clr_err = 0;
  cfg_out = 0;
  cfg_err = 0;
  irq_err = 0;
  level_out = 0;	
  
  if (cmd_exe)
    {
      sc_uint<32> pwdata = PWDATA;
      switch (pwdata)
	{
	case CMD_CLR:   
	  if (!play_r)
	    clr = 1;
	  else
	    clr_err = 1;
	  break;
	case CMD_CFG:   
	  if (!play_r)
	    cfg_out = 1;	  
	  else
	    cfg_err = 1;
	  break;
	case CMD_LEVEL: 
	  level_out = 1;
	  break;
	case CMD_START: 
	  start = 1;
	  break;
	case CMD_STOP:  
	  stop = 1;
	  break;
	case CMD_IRQACK:  
	  irqack = 1;
	  break;
	default:
	  cmd_err = 1;
	  break;
	}
    }
  
  // wait counter
  wctr_ns = wctr_r;
  if (wctr_r.read() == 0)
    {
      if (PSEL && !PENABLE && PWRITE && rindex == CMD_REG_INDEX)	  
	wctr_ns = 1;
    }
  else if (wctr_r.read() < CMD_WAIT_STATES)
    wctr_ns = wctr_r.read() + 1;
  else
    wctr_ns = 0;

  // irq next state
  if (!(play_r.read()) || stop)
    irq_ns = 0; 
  else if (irqack)
    irq_ns = 0;	       
  else if (play_r.read() && req_r == 1 && ( ((ABUF0_START_INDEX + rctr_r.read()) == ABUF0_END_INDEX-1)  || 
					     ((ABUF0_START_INDEX + rctr_r.read()) == ABUF1_END_INDEX-1)))
    {
      if (irq_r)
	{
	  irq_ns = 1;
	  irq_err = 1;
	}
      else
	{
	  irq_ns = 1;
	  irq_err = 0;
	}
    }
  else
    irq_ns = irq_r;

  // Outputs
  clr_out = clr;
  irq_out = irq_r;
  play_out = play_r;
  
  if (play_r)
    tick_out = req_r;
  else
    tick_out = 0;

  sc_bv<DSP_REGISTERS*32>  dsp_regs;  
  for(int i=0; i < DSP_REGISTERS; ++i)
    dsp_regs.range((i+1)*24-1, i*24) = (sc_bv<32>)(rbank_ns[DSP_REGS_START_INDEX+i]);
  dsp_regs_out = dsp_regs;

  cfg_reg_out = rbank_r[CFG_REG_INDEX];
  level_reg_out = rbank_r[LEVEL_REG_INDEX];
	
  audio0_out = (sc_int<24>) (rbank_r[ABUF0_START_INDEX + rctr_r.read()   ].read());
  audio1_out = (sc_int<24>) (rbank_r[ABUF0_START_INDEX + rctr_r.read() +1].read());	
    

  // Register bank control
  for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
    rbank_ns[i] = rbank_r[i];

  if (clr)
    {
      for (int i = ABUF0_START_INDEX; i <= ABUF1_END_INDEX; ++i)
	rbank_ns[i] = 0;
    }

  if (write)
    rbank_ns[rindex].write(PWDATA);
  
  if (cmd_err || clr_err || cfg_err || irq_err || start || stop)
    {
      sc_uint<32> tmp = rbank_r[STATUS_REG_INDEX].read();
      if (cmd_err)
	tmp[STATUS_CMD_ERR] = 1;      
      if (clr_err)
	tmp[STATUS_CLR_ERR] = 1;      
      if (cfg_err)
	tmp[STATUS_CFG_ERR] = 1;      
      if (irq_err)
	tmp[STATUS_IRQ_ERR] = 1;      
      if (start)
	tmp[STATUS_PLAY] = 1;      
      else if (stop)
	tmp[STATUS_PLAY] = 0;      
      rbank_ns[STATUS_REG_INDEX].write(tmp);
    }
  
  // Play mode control
  if (start == 1)
    play_ns = 1;
  else if (stop == 1)
    play_ns = 0;		      
  else
    play_ns = play_r;

  // Read counter control  
  rctr_ns = rctr_r;    
  if (clr == 1)
    rctr_ns = 0;	     
  else if (req_r == 1)
    {
      if (rctr_r.read() < 4*AUDIO_BUFFER_SIZE-2)
	rctr_ns = rctr_r.read() + 2;
      else
	rctr_ns = 0;
    }
  
  // tick register
  if (play_r.read() && req_in)
    req_ns = 1;
  else
    req_ns = 0;
}

#endif











#else

void control_unit::control_unit_proc()
{

 RESET_REGION: {
    wctr_r = 0;
    for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
      rbank_r[i] = 0;
    irq_r = 0;
    play_r = 0;
    rctr_r = 0;
    req_r = 0;
    wait();
  }

  while(1)
    {

      ////////////////////////////////////////////////////////////////////
      // Input decoding
      ////////////////////////////////////////////////////////////////////

      // Internal address decoding
      if(PSEL == 1)
	rindex = (PADDR.read() - AUDIOPORT_START_ADDRESS) >> 2;
      else
	rindex = 0;

      // write decoder
      write = 0;
      cmd_exe = 0;
      if (wctr_r.read() == 0 && PSEL && PENABLE == 1 && PWRITE == 1)
	{
	  write = 1;
	  if (rindex == CMD_REG_INDEX)
	    cmd_exe = 1;
	}
      
      // Command decoding
      start = 0;
      stop = 0;
      clr = 0;
      irqack = 0;
      cmd_err = 0;
      clr_err = 0;
      cfg_out = 0;
      cfg_err = 0;
      irq_err = 0;
      level_out = 0;	
  
      if (cmd_exe)
	{
	  sc_uint<32> pwdata = PWDATA;
	  switch (pwdata)
	    {
	    case CMD_CLR:   
	      if (!play_r)
		clr = 1;
	      else
		clr_err = 1;
	      break;
	    case CMD_CFG:   
	      if (!play_r)
		cfg_out = 1;	  
	      else
		cfg_err = 1;
	      break;
	    case CMD_LEVEL: 
	      level_out = 1;
	      break;
	    case CMD_START: 
	      start = 1;
	      break;
	    case CMD_STOP:  
	      stop = 1;
	      break;
	    case CMD_IRQACK:  
	      irqack = 1;
	      break;
	    case CMD_NOP:
	      break;
	    default:
	      cmd_err = 1;
	      break;
	    }
	}
  
      ////////////////////////////////////////////////////////////////////
      // Register next states
      ////////////////////////////////////////////////////////////////////

      // wait counter
      wctr_ns = wctr_r;
      if (wctr_r.read() == 0)
	{
	  if (PSEL && !PENABLE && PWRITE && rindex == CMD_REG_INDEX)	  
	    wctr_ns = 1;
	}
      else if (wctr_r.read() < CMD_WAIT_STATES)
	wctr_ns = wctr_r.read() + 1;
      else
	wctr_ns = 0;

      // irq next state
      if (!(play_r.read()) || stop)
	irq_ns = 0; 
      else if (irqack)
	irq_ns = 0;	       
      else if (play_r.read() && req_r == 1 && ( ((ABUF0_START_INDEX + rctr_r.read()) == ABUF0_END_INDEX-1)  || 
						 ((ABUF0_START_INDEX + rctr_r.read()) == ABUF1_END_INDEX-1)))
	{
	  if (irq_r)
	    {
	      irq_ns = 1;
	      irq_err = 1;
	    }
	  else
	    {
	      irq_ns = 1;
	      irq_err = 0;
	    }
	}
      else
	irq_ns = irq_r;
  
      // Read counter control  
      rctr_ns = rctr_r;    
      if (clr == 1)
	rctr_ns = 0;	     
      else if (req_r == 1)
	{
	  if (rctr_r.read() < 4*AUDIO_BUFFER_SIZE-2)
	    rctr_ns = rctr_r.read() + 2;
	  else
	    rctr_ns = 0;
	}
  
      // tick register
      if (play_r.read() && req_in)
	req_ns = 1;
      else
	req_ns = 0;

      // Register bank control
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	rbank_ns[i] = rbank_r[i];

      if (clr)
	{
	  for (int i = ABUF0_START_INDEX; i <= ABUF1_END_INDEX; ++i)
	    rbank_ns[i] = 0;
	}

      if (write)
	rbank_ns[rindex] = PWDATA;
  
      if (cmd_err || clr_err || cfg_err || irq_err || start || stop)
	{
	  sc_uint<32> tmp = rbank_r[STATUS_REG_INDEX].read();
	  if (cmd_err)
	    tmp[STATUS_CMD_ERR] = 1;      
	  if (clr_err)
	    tmp[STATUS_CLR_ERR] = 1;      
	  if (cfg_err)
	    tmp[STATUS_CFG_ERR] = 1;      
	  if (irq_err)
	    tmp[STATUS_IRQ_ERR] = 1;      
	  if (start)
	    tmp[STATUS_PLAY] = 1;      
	  else if (stop)
	    tmp[STATUS_PLAY] = 0;      
	  rbank_ns[STATUS_REG_INDEX] = tmp;
	}

      // Play mode control
      if (start == 1)
	play_ns = 1;
      else if (stop == 1)
	play_ns = 0;		      
      else
	play_ns = play_r;

      ////////////////////////////////////////////////////////////////////
      // Register update
      ////////////////////////////////////////////////////////////////////

      wctr_r = wctr_ns;
      for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
	rbank_r[i] =  rbank_ns[i];
      irq_r = irq_ns;
      play_r = play_ns;
      rctr_r = rctr_ns;
      req_r = req_ns;

      ////////////////////////////////////////////////////////////////////
      // Register decoding
      ////////////////////////////////////////////////////////////////////

      // PRDATA mux
      if (PSEL)
	PRDATA = rbank_ns[rindex];
      else
	PRDATA = 0;
  
  
      // PREADY decoder
      if (wctr_ns == 0)
	PREADY = 1;
      else
	PREADY = 0;
      
      // PSLVERR
      PSLVERR = 0;
  
      // Outputs
      clr_out = clr;
      irq_out = irq_ns;
      play_out = play_ns;
  
      if (play_ns)
	tick_out = req_ns;
      else
	req_out = 0;

      sc_bv<DSP_REGISTERS*32>  dsp_regs;  
      for(int i=0; i < DSP_REGISTERS; ++i)
	dsp_regs.range((i+1)*24-1, i*24) = (sc_bv<32>)(rbank_ns[DSP_REGS_START_INDEX+i]);
      dsp_regs_out = dsp_regs;
      
      cfg_reg_out = rbank_ns[CFG_REG_INDEX];
      level_reg_out = rbank_ns[LEVEL_REG_INDEX];
	
      audio0_out = (sc_int<24>) (rbank_ns[ABUF0_START_INDEX + rctr_ns]);
      audio1_out = (sc_int<24>) (rbank_ns[ABUF0_START_INDEX + rctr_ns +1]);
    
      wait();
    }
}
#endif


#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(control_unit);
#endif
