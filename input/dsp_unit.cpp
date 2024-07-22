// 1.
#include "dsp_unit.h"

void dsp_unit::dsp_proc()
{
  // Local variables
  bool                tick_in_v;
  bool                clr_in_v;
  sc_int<DATABITS>    audio0_in_v;
  sc_int<DATABITS>    audio1_in_v;
  sc_int<ACCBITS>     fir_30l_accum, fir_30r_accum, fir_330l_accum, fir_330r_accum;
  sc_int<SUMBITS>     left_sum, right_sum;
  sc_int<DATABITS>    filtered0_v;
  sc_int<DATABITS>    filtered1_v;
  sc_int<DATABITS+16> scaled0_v;
  sc_int<DATABITS+16> scaled1_v;
  sc_int<DATABITS>    dsp0_out_v;
  sc_int<DATABITS>    dsp1_out_v;
  
  ///////////////////////////////////////////////////////////
  // Reset Section
  ///////////////////////////////////////////////////////////
  
  // 2.
 RESET_REGION: {
    dsp0_out.write(0);
    dsp1_out.write(0);
    valid_out.write(0);
    
    // To do: reset all member variables you declared -------
    
    DATA_RESET_LOOP: for (int i=0; i < FILTER_TAPS; ++i)
      {
	data0_r[i] = 0;
	data1_r[i] = 0;
      }

    // ------------------------------------------------------

  RESET_WAIT: wait();
  }
  
  ///////////////////////////////////////////////////////////
  // Processing Loop
  ///////////////////////////////////////////////////////////
  
 PROCESS_LOOP: while(true)
    {

    INPUT_REGION: {
      // 3.
      tick_in_v    = 0;
      clr_in_v     = 0;
      audio0_in_v  = 0;
      audio1_in_v  = 0;

      read_inputs(tick_in_v, clr_in_v, audio0_in_v, audio1_in_v);
      }

    PROCESSING_REGION: {
	
	// 4.
	if (clr_in_v)
	  {
	    // ----- To do: add code for clear operation  ---------------
	    
	    for (int i = 0; i < FILTER_TAPS; ++i)
        {
        	data0_r[i] = 0;
            data1_r[i] = 0;
        }

	    // ----------------------------------------------------------

	    dsp0_out_v = 0;
	    dsp1_out_v = 0;
	  }

	// 5.
	else if (tick_in_v)
	  {
	    
	    if (!filter_r.read())
	      {
		filtered0_v = audio0_in_v;
		filtered1_v = audio1_in_v;
	      }
	    else
	      {
		// ----- To do: add code for filter --------------------
		
		// Shift registers for new input
        SHIFT_LOOP: for (int i = FILTER_TAPS-1; i > 0; --i)
        {
        	data0_r[i] = data0_r[i-1];
            data1_r[i] = data1_r[i-1];
        }
        data0_r[0] = audio0_in_v;
        data1_r[0] = audio1_in_v;

        // FIR filters
        fir_30l_accum = 0;
        fir_30r_accum = 0;
        fir_330l_accum = 0;
        fir_330r_accum = 0;

        FIR_LOOP: for (int i = 0; i < FILTER_TAPS; ++i)
        {
        	fir_30l_accum += data0_r[i] * dsp_regs_r[i].read();
            fir_30r_accum += data1_r[i] * dsp_regs_r[i + FILTER_TAPS].read();
            fir_330l_accum += data0_r[i] * dsp_regs_r[i + 2*FILTER_TAPS].read();
            fir_330r_accum += data1_r[i] * dsp_regs_r[i + 3*FILTER_TAPS].read();
        }

        left_sum = fir_30l_accum + fir_330r_accum;
        right_sum = fir_30r_accum + fir_330l_accum;

        // Scale and assign filtered values
        filtered0_v = left_sum >> (31 + 1);
        filtered1_v = right_sum >> (31 + 1);
		

		// ------------------------------------------------
	      }
	    
	    scaled0_v = filtered0_v * level0_r.read();
	    scaled0_v >>= 15;
	    scaled1_v = filtered1_v * level1_r.read();
	    scaled1_v >>= 15;
	    
	    if (mono_r.read())
	      {
		// ----- To do: add code for mono mode ------------
		
		sc_int<DATABITS + 16> mono_v = (scaled0_v + scaled1_v) >> 1;
        scaled0_v = mono_v;
        scaled1_v = mono_v;

		// ------------------------------------------------
	      }
	    
	    dsp0_out_v = (sc_int<DATABITS>) scaled0_v;
	    dsp1_out_v = (sc_int<DATABITS>) scaled1_v;
	  }
      } // PROCESSING_REGION END


      // 6.
    OUTPUT_REGION: {
	write_outputs(dsp0_out_v, dsp1_out_v);
      }
      
    }
}

// 7.
#pragma design modulario<in>
void dsp_unit::read_inputs(bool &tick, bool &clr, sc_int<DATABITS> &audio0, sc_int<DATABITS> &audio1)
{
 INPUT_LOOP: do {
    wait();
    tick = tick_in.read();
    clr =  clr_in.read();
  } while (!tick && !clr); 
  audio0 = audio0_in.read();	  
  audio1 = audio1_in.read();	  
}

// 8.
#pragma design modulario<out>
void dsp_unit::write_outputs(sc_int<DATABITS> dsp0, sc_int<DATABITS> dsp1)
{
  valid_out.write(1);
  dsp0_out.write(dsp0);
  dsp1_out.write(dsp1);
  wait();
  valid_out.write(0);
}

// 9.
void dsp_unit::regs_proc()
{
  sc_uint<32>             level_reg;
  sc_bv<DSP_REGISTERS*32> dsp_regs;

  if (rst_n.read() == 0)
    {
    COEFF_RESET_LOOP: for (int i=0; i < DSP_REGISTERS; ++i)
	{
	  dsp_regs_r[i].write(0);
	}
      level0_r.write(0);
      level1_r.write(0);
      filter_r.write(0);
      mono_r.write(0);
    }
  else
    {
      if (cfg_in.read())
	{
	  filter_r.write(cfg_reg_in.read()[CFG_FILTER]);	
	  mono_r.write(cfg_reg_in.read()[CFG_MONO]);	
	  dsp_regs = dsp_regs_in.read();
	COEFF_WRITE_LOOP: for (int i=0; i < DSP_REGISTERS; ++i)
	    {
	      sc_int<32> c;
	      c = dsp_regs.range((i+1)*32-1, i*32).to_int();
	      dsp_regs_r[i].write(c);
	    }
	}
      else if (level_in.read())
	{
	  level_reg = level_reg_in.read();
	  level0_r.write(level_reg.range(15,0).to_uint());
	  level1_r.write(level_reg.range(31,16).to_uint());
	}
    }
}

#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(dsp_unit);
#endif

