#ifndef cdc_unit_h
#define cdc_unit_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "cdc_unit_sc_foreign_module.h"
#else


SC_MODULE(cdc_unit) {
public:
  sc_in<bool>              clk;
  sc_in<bool>              rst_n;
  sc_in<bool>              mclk_in;
  sc_out<bool>             mclk;
  sc_out<bool>             mrst_n;
  sc_in<bool>              test_mode_in;
  sc_in<bool>              tick_in;
  sc_in< sc_int<24> >      dsp0_in;
  sc_in< sc_int<24> >      dsp1_in;
  sc_out<bool>             tick_out;
  sc_out< sc_int<24> >     dsp0_out;
  sc_out< sc_int<24> >     dsp1_out;
  
  sc_in<bool>              cfg_in;
  sc_in< sc_uint<32> >     cfg_reg_in;
  sc_out<bool>             cfg_out;
  sc_out< sc_uint<32> >    cfg_reg_out;
  
  sc_in<bool>              req_in;
  sc_out<bool>             req_out;
  
  sc_in<bool>              play_in;
  sc_out<bool>             play_out;
  
  sc_signal<bool> srst_n;
  sc_signal<bool> rst_sff1;
  sc_signal<bool> play_sff1;
  sc_signal<bool> req_sff1;
  sc_signal<bool> req_sff2;
  sc_signal<bool> req_sff3;            
  
  sc_signal<sc_uint<3>> cfg_tx_st;
  sc_signal<sc_uint<3>> cfg_rx_st;    
  sc_signal<sc_uint<3>> cfg_tx_ns;
  sc_signal<sc_uint<3>> cfg_rx_ns;    
  sc_signal<bool> cfg_tx_en;
  sc_signal<sc_uint<32>> cfg_tx_r;
  sc_signal<sc_uint<32>> cfg_rx_r;    
  sc_signal<bool> cfg_req;
  sc_signal<bool> cfg_req_sff1;
  sc_signal<bool> cfg_req_sff2;        
  sc_signal<bool> cfg_ack;
  sc_signal<bool> cfg_ack_sff1;
  sc_signal<bool> cfg_ack_sff2;    
  
  sc_signal<sc_uint<3>> tick_tx_st;
  sc_signal<sc_uint<3>> tick_rx_st;    
  sc_signal<sc_uint<3>> tick_tx_ns;
  sc_signal<sc_uint<3>> tick_rx_ns;    
  sc_signal<bool> tick_tx_en;
  sc_signal<sc_uint<48>> tick_tx_r;
  sc_signal<sc_uint<48>> tick_rx_r;    
  sc_signal<bool> tick_req;
  sc_signal<bool> tick_req_sff1;
  sc_signal<bool> tick_req_sff2;        
  sc_signal<bool> tick_ack;
  sc_signal<bool> tick_ack_sff1;
  sc_signal<bool> tick_ack_sff2;    
  
  void comb();
    void reset_sync();    
    void clk2mclk();
    void mclk2clk();
    
    SC_CTOR(cdc_unit)
    {
      SC_METHOD(comb);
      sensitive << test_mode_in << clk << mclk_in << rst_n << srst_n << req_sff2 << req_sff3
	        << cfg_in << cfg_tx_st << cfg_rx_st << cfg_rx_r << cfg_req_sff2 << cfg_ack_sff2
	        << tick_in << tick_tx_st << tick_rx_st << tick_rx_r << tick_req_sff2 << tick_ack_sff2;	

      SC_METHOD(reset_sync);
      sensitive << mclk_in.pos() << rst_n.neg();
      
      SC_METHOD(clk2mclk);
      sensitive << mclk_in.pos() << srst_n;

      SC_METHOD(mclk2clk);
      sensitive << clk.pos() << rst_n.neg();
    }

};




#endif
#endif

