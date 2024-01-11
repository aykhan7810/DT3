#include "cdc_unit.h"

void cdc_unit::comb()
{
  if (test_mode_in.read()) {
    mclk.write(clk.read());
    mrst_n.write(rst_n.read());
  } else {
    mclk.write(mclk_in.read());
    mrst_n.write(srst_n.read());
  }

  if (req_sff2.read() && !req_sff3.read())
    req_out.write(1);
  else
    req_out.write(0);

  switch(cfg_tx_st.read())
    {
    case 1:
      cfg_req.write(0);            
      if(cfg_in.read() && !cfg_ack_sff2.read()) {
	cfg_tx_en.write(1);
	cfg_tx_ns.write(2);
      } else {
	cfg_tx_en.write(0);
	cfg_tx_ns.write(1);
      }
      break;
    case 2:
      cfg_tx_en.write(0);
      cfg_req.write(1);      
      if(!cfg_ack_sff2.read()) {
	cfg_tx_ns.write(2);
      } else {
	cfg_tx_ns.write(4);
      }
      break;
    case 4:
      cfg_tx_en.write(0);      
      cfg_req.write(0);
      if(!cfg_ack_sff2.read()) {
	cfg_tx_ns.write(1);
      } else {
	cfg_tx_ns.write(4);
      }
      break;
  }

  switch(cfg_rx_st.read())
    {
    case 1:
      cfg_out.write(0);      
      cfg_ack.write(0);            
      if(cfg_req_sff2.read()) {
	cfg_rx_ns.write(2);
      } else {
	cfg_rx_ns.write(1);
      }
      break;
    case 2:
      cfg_out.write(1);
      cfg_ack.write(1);                  
      cfg_rx_ns.write(4);
      break;
    case 4:
      cfg_out.write(0);
      if(!cfg_req_sff2.read()) {
	cfg_ack.write(0);
	cfg_rx_ns.write(1);
      } else {
	cfg_ack.write(1);
	cfg_rx_ns.write(4);
      }
      break;
  }

  cfg_reg_out.write(cfg_rx_r);

  
  switch(tick_tx_st.read())
    {
    case 1:
      tick_req.write(0);            
      if(tick_in.read() && !tick_ack_sff2.read()) {
	tick_tx_en.write(1);
	tick_tx_ns.write(2);
      } else {
	tick_tx_en.write(0);
	tick_tx_ns.write(1);
      }
      break;
    case 2:
      tick_tx_en.write(0);
      tick_req.write(1);      
      if(!tick_ack_sff2.read()) {
	tick_tx_ns.write(2);
      } else {
	tick_tx_ns.write(4);
      }
      break;
    case 4:
      tick_tx_en.write(0);      
      tick_req.write(0);
      if(!tick_ack_sff2.read()) {
	tick_tx_ns.write(1);
      } else {
	tick_tx_ns.write(4);
      }
      break;
  }

  switch(tick_rx_st.read())
    {
    case 1:
      tick_out.write(0);      
      tick_ack.write(0);            
      if(tick_req_sff2.read()) {
	tick_rx_ns.write(2);
      } else {
	tick_rx_ns.write(1);
      }
      break;
    case 2:
      tick_out.write(1);
      tick_ack.write(1);                  
      tick_rx_ns.write(4);
      break;
    case 4:
      tick_out.write(0);
      if(!tick_req_sff2.read()) {
	tick_ack.write(0);
	tick_rx_ns.write(1);
      } else {
	tick_ack.write(1);
	tick_rx_ns.write(4);
      }
      break;
  }

  dsp0_out.write( (sc_int<24>) tick_rx_r.read().range(23,0) );
  dsp1_out.write( (sc_int<24>) tick_rx_r.read().range(47,24) );
}

void cdc_unit::reset_sync()
{
  if(!rst_n.read()) {
    rst_sff1.write(0);
    srst_n.write(0);
  } else {
    rst_sff1.write(1);
    srst_n.write(rst_sff1.read());
  }

}
  
void cdc_unit::clk2mclk()
{
  if(!srst_n.read()) {
    play_sff1.write(0);
    play_out.write(0);

    cfg_rx_st.write(1);
    cfg_rx_r.write(0);
    cfg_req_sff1.write(0);
    cfg_req_sff2.write(0);    

    tick_rx_st.write(1);
    tick_rx_r.write(0);
    tick_req_sff1.write(0);
    tick_req_sff2.write(0);    
  } else {
    play_sff1.write(play_in.read());
    play_out.write(play_sff1.read());

    cfg_rx_st.write(cfg_rx_ns.read());
    cfg_req_sff1.write(cfg_req.read());
    cfg_req_sff2.write(cfg_req_sff1.read());    
    if (cfg_req_sff2.read()) {
      cfg_rx_r.write(cfg_tx_r.read());
    }
    
    tick_rx_st.write(tick_rx_ns.read());
    tick_req_sff1.write(tick_req.read());
    tick_req_sff2.write(tick_req_sff1.read());    
    if (tick_req_sff2.read()) {
      tick_rx_r.write(tick_tx_r.read());
    }
  }

}

void cdc_unit::mclk2clk()
{
  if(!srst_n.read()) {
    req_sff1.write(0);
    req_sff2.write(0);
    req_sff3.write(0);        

    cfg_tx_st.write(1);
    cfg_tx_r.write(0);
    cfg_ack_sff1.write(0);
    cfg_ack_sff2.write(0);    
    
    tick_tx_st.write(1);
    tick_tx_r.write(0);
    tick_ack_sff1.write(0);
    tick_ack_sff2.write(0);    

  } else {
    req_sff1.write(req_in.read());
    req_sff2.write(req_sff1.read());
    req_sff3.write(req_sff2.read());        

    cfg_tx_st.write(cfg_tx_ns.read());
    if (cfg_tx_en.read()) {
      cfg_tx_r.write(cfg_reg_in.read());
    }
    cfg_ack_sff1.write(cfg_ack.read());
    cfg_ack_sff2.write(cfg_ack_sff1.read());    
    
    tick_tx_st.write(tick_tx_ns.read());
    if (tick_tx_en.read()) {
      sc_uint<48> concat;
      concat.range(47,24) = (sc_uint<24>)(dsp1_in.read());
      concat.range(23,0) =  (sc_uint<24>)(dsp0_in.read());
      tick_tx_r.write(concat);
    }
    tick_ack_sff1.write(tick_ack.read());
    tick_ack_sff2.write(tick_ack_sff1.read());    
  }  
}

#if defined(MTI_SYSTEMC)
SC_MODULE_EXPORT(cdc_unit);
#endif
