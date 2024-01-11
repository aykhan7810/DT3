#include "i2s_unit.h"

#define STANDBY 0
#define PLAY    1

void i2s_unit::proc()
{
 RESET_REGION: {
    ws_out.write(0);
    sck_out.write(0);
    sdo_out.write(0);
    state_r = STANDBY;
    inreg_r = 0;
    srg_r = 0;
    ctr_r = 0;
    wait();
  }
  
  while(1)
    {


      ////////////////////////////////////////////////////////////////////////////
      // Registers
      ////////////////////////////////////////////////////////////////////////////      

      switch(state_r) {
      case STANDBY:
	srg_r = 0;
	inreg_r = 0;
	ctr_r = 0;
	if (play_in.read() == 1)
	  state_r = PLAY;
	if (cfg_in.read() == 1)
	  cfg_r = (0x3 & cfg_reg_in.read());
	break;

      case PLAY:

	  
	switch(cfg_r) {
	    
	case 0:

	  if (ctr_r == 7 && play_in.read() == 0)
	    state_r = STANDBY;
	  
	  if (play_in.read() == 1 && ctr_r == 3) {
	    srg_r = inreg_r;
	  } else if (ctr_r.range(2,0) == 3) {
	    srg_r <<= 1;
	  }
	    
	  if (ctr_r < 383)
	    ctr_r = ctr_r + 1;
	  else
	    ctr_r = 0;
	  break;

	case 1:

	  if (ctr_r == 3 && play_in.read() == 0)
	    state_r = STANDBY;
	  
	  if (play_in.read() == 1 && ctr_r == 1) {
	    srg_r = inreg_r;
	  } else if (ctr_r.range(1,0) == 1) {
	    srg_r <<= 1;
	  }

	  if (ctr_r < 191)
	    ctr_r = ctr_r + 1;
	  else
	    ctr_r = 0;

	  break;

	case 2:

	  if (ctr_r == 1 && play_in.read() == 0)
	    state_r = STANDBY;

	  if (play_in.read() == 1 && ctr_r == 0) {
	    srg_r = inreg_r;
	  } else if (ctr_r[0] == 0) {
	    srg_r <<= 1;
	  }
	    
	  if (ctr_r < 95)
	    ctr_r = ctr_r + 1;
	  else
	    ctr_r = 0;

	  break;

	default:

	  if (ctr_r == 7 && play_in.read() == 0)
	    state_r = STANDBY;
	  
	  if (play_in.read() == 1 && ctr_r == 4) {
	    srg_r = inreg_r;
	  } else if (ctr_r.range(2,0) == 4) {
	    srg_r <<= 1;
	  }
	    
	  if (ctr_r < 383)
	    ctr_r = ctr_r + 1;
	  else
	    ctr_r = 0;

	  break;
	} // cfg_r

	// inreg must be updated after srg
	if (tick_in.read() == 1) 
	  {
	    inreg_r.range(47,24) = (sc_uint<24>)(audio0_in.read());
	    inreg_r.range(23,0) = (sc_uint<24>)(audio1_in.read());	      	      
	  }

      } // state_r


      ////////////////////////////////////////////////////////////////////////////
      // Output decoding
      ////////////////////////////////////////////////////////////////////////////      
      
      switch(state_r) {
      case STANDBY:
	sdo_out.write( srg_r[47] );
	sck_out.write( 0 );
	ws_out.write( 0 );
	req_out.write( 0 );
	break;

      case PLAY:

	sdo_out.write( srg_r[47] );

	switch(cfg_r) {
	    
	case 0:
	  if (play_in.read() == 1 && ctr_r == 3)
	    req_out.write(1);
	  else
	    req_out.write(0);	    

	  if ( (ctr_r & 0x7) < 4)
	    sck_out.write(1);
	  else
	    sck_out.write(0);	      

	  if ( ctr_r  < 188 || ctr_r > 379)
	    ws_out.write(0);
	  else
	    ws_out.write(1);	      
	    
	  break;

	case 1:

	  if (play_in.read() == 1 && ctr_r == 1)
	    req_out.write(1);
	  else
	    req_out.write(0);	      
	    
	  if ( (ctr_r & 0x3) < 2)
	    sck_out.write(1);
	  else
	    sck_out.write(0);	      

	  if ( ctr_r  < 94 || ctr_r > 189)
	    ws_out.write(0);
	  else
	    ws_out.write(1);	      
	    	    
	  break;

	case 2:
	  if (play_in.read() == 1 && ctr_r == 0)
	    req_out.write(1);
	  else
	    req_out.write(0);	      

	  if (ctr_r[0] == 0)
	    sck_out.write(1);
	  else
	    sck_out.write(0);	      

	  if ( ctr_r  < 47 || ctr_r > 94)
	    ws_out.write(0);
	  else
	    ws_out.write(1);	      
	    
	  break;

	default:

	  if (play_in.read() == 1 && ctr_r == 3)
	    req_out.write(1);
	  else
	    req_out.write(0);	      

	  if ( (ctr_r & 0x7) < 4)
	    sck_out.write(1);
	  else
	    sck_out.write(0);	      

	  if ( ctr_r  < 188 || ctr_r > 379)
	    ws_out.write(0);
	  else
	    ws_out.write(1);	      
	    
	  break;
	} // cfg_r
	  
      } // state_r

      wait();
    }
}

#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(i2s_unit);
#endif
