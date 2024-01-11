#ifndef dsp_unit_top_h
#define dsp_unit_top_h

// 1.

#include "dsp_unit.h"
#include "dsp_unit_tb.h"

// 2.
SC_MODULE(dsp_unit_top) {
  sc_clock                              clk;
  sc_signal<bool>                       rst_n;
  sc_signal < sc_int<DATABITS> >        audio0_in;
  sc_signal < sc_int<DATABITS> >        audio1_in;
  sc_signal < bool >                    tick_in;
  sc_signal < bool >                    cfg_in;
  sc_signal < bool >                    level_in;
  sc_signal < bool >                    clr_in;
  sc_signal < sc_bv<DSP_REGISTERS*32> > dsp_regs_in;
  sc_signal  < sc_uint<32> >            cfg_reg_in;
  sc_signal  < sc_uint<32> >            level_reg_in;
  sc_signal < sc_int<DATABITS> >        dsp0_out;
  sc_signal < sc_int<DATABITS> >        dsp1_out;
  sc_signal < bool >                    valid_out;

  dsp_unit dsp_unit_inst; 
  dsp_unit_tb dsp_unit_tb_inst;

  void reset_thread();

 SC_CTOR(dsp_unit_top) :
  clk("clk", CLK_PERIOD, SC_NS, 0.5),
#ifndef HLS_RTL
    dsp_unit_inst("dsp_unit_inst"),
#else
    dsp_unit_inst("dsp_unit_inst", "work.dsp_unit"),
#endif
    dsp_unit_tb_inst("dsp_unit_tb_inst")    
  {
    SC_THREAD(reset_thread);
    dont_initialize();
    sensitive << clk.posedge_event();

    dsp_unit_inst.clk(clk);
    dsp_unit_inst.rst_n(rst_n);
    dsp_unit_inst.audio1_in(audio1_in);
    dsp_unit_inst.audio0_in(audio0_in);
    dsp_unit_inst.tick_in(tick_in);
    dsp_unit_inst.cfg_in(cfg_in);
    dsp_unit_inst.level_in(level_in);
    dsp_unit_inst.clr_in(clr_in);
    dsp_unit_inst.cfg_reg_in(cfg_reg_in);
    dsp_unit_inst.level_reg_in(level_reg_in);
    dsp_unit_inst.dsp0_out(dsp0_out);
    dsp_unit_inst.dsp1_out(dsp1_out);
    dsp_unit_inst.valid_out(valid_out);
    dsp_unit_inst.dsp_regs_in(dsp_regs_in);

    dsp_unit_tb_inst.clk(clk);
    dsp_unit_tb_inst.rst_n(rst_n);
    dsp_unit_tb_inst.audio0_in(audio0_in);
    dsp_unit_tb_inst.audio1_in(audio1_in);
    dsp_unit_tb_inst.tick_in(tick_in);
    dsp_unit_tb_inst.cfg_in(cfg_in);
    dsp_unit_tb_inst.level_in(level_in);
    dsp_unit_tb_inst.clr_in(clr_in);
    dsp_unit_tb_inst.cfg_reg_in(cfg_reg_in);
    dsp_unit_tb_inst.level_reg_in(level_reg_in);
    dsp_unit_tb_inst.dsp0_out(dsp0_out);
    dsp_unit_tb_inst.dsp1_out(dsp1_out);
    dsp_unit_tb_inst.valid_out(valid_out);
    dsp_unit_tb_inst.dsp_regs_in(dsp_regs_in);
  }

};

#endif
