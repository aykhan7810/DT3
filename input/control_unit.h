#ifndef control_unit_h
#define control_unit_h

#include "systemc_headers.h"
#include "audioport_defs.h"

#ifdef HLS_RTL
#include "control_unit_sc_foreign_module.h"
#else

#define control_unit_as_rtl 1

SC_MODULE(control_unit) {
 public:
  sc_in_clk              clk;
  sc_in<bool>            rst_n;
  sc_in < sc_uint<32> >  PADDR;
  sc_in < sc_uint<32> >  PWDATA;
  sc_in < bool >         PENABLE;
  sc_in < bool >         PSEL;
  sc_in < bool >         PWRITE;
  sc_out < sc_uint<32> > PRDATA;
  sc_out < bool >        PREADY;
  sc_out < bool >        PSLVERR;
  sc_out < bool >        irq_out;
  sc_out < sc_uint<32> > cfg_reg_out;
  sc_out <bool>          cfg_out;
  sc_out < sc_uint<32> > level_reg_out;
  sc_out <bool>          level_out;
  sc_out <bool>          clr_out;
  sc_out < sc_bv<DSP_REGISTERS*32> >  dsp_regs_out;
  sc_in  <bool>          req_in;
  sc_out < sc_int<24> >  audio0_out;
  sc_out < sc_int<24> >  audio1_out;
  sc_out <bool>          tick_out;
  sc_out <bool>          play_out;

#ifdef control_unit_as_rtl
  void control_logic_proc();
  void control_regs_proc();
#else
  void control_unit_proc();
#endif

  sc_signal < sc_uint<32> >  rbank_r[AUDIOPORT_REGISTERS];
  sc_signal < sc_uint<3>  >  wctr_r;
  sc_signal < bool >         irq_r;
  sc_signal < bool >         play_r;
  sc_signal < bool >         req_r;
  sc_signal < sc_uint<7> >   rctr_r;
#ifdef control_unit_as_rtl
  sc_signal < sc_uint<32> >  rbank_ns[AUDIOPORT_REGISTERS];
  sc_signal < sc_uint<3>  >  wctr_ns;
  sc_signal < bool >         irq_ns;
  sc_signal < bool >         play_ns;
  sc_signal < bool >         req_ns;
  sc_signal < sc_uint<7> >  rctr_ns;
#else
  sc_uint<32>  rbank_ns[AUDIOPORT_REGISTERS];
  sc_uint<3>   wctr_ns;
  bool         irq_ns;
  bool         play_ns;
  bool         req_ns;
  sc_uint<10>  rctr_ns;
#endif
  
  sc_signal<sc_uint<RINDEX_BITS>>     rindex;
  sc_signal<bool> ready;
  sc_signal<bool> write;
  sc_signal<bool> cmd_exe;
  sc_signal<bool> start;
  sc_signal<bool> stop;
  sc_signal<bool> clr;
  sc_signal<bool> irqack;
  sc_signal<bool> cmd_err;
  sc_signal<bool> clr_err;
  sc_signal<bool> cfg_err;
  sc_signal<bool> irq_err;
  
 SC_CTOR(control_unit) :
  clk("clk"),
    rst_n("rst_n"),
    PADDR("PADDR"),
    PWDATA("PWDATA"),
    PENABLE("PENABLE"),
    PSEL("PSEL"),
    PWRITE("PWRITE"),
    PRDATA("PRDATA"),
    PREADY("PREADY"),
    PSLVERR("PSLVERR"),
    irq_out("irq_out"),
    cfg_reg_out("cfg_reg_out"),
    cfg_out("cfg_out"),
    level_reg_out("level_reg_out"),
    level_out("level_out"),
    clr_out("clr_out"),
    dsp_regs_out("dsp_regs_out"),
    req_in("req_in"),
    audio0_out("audio0_out"),
    audio1_out("audio1_out"),
    tick_out("tick_out"),
    play_out("play_out"),
    //    rbank_r("rbank_r"),
    wctr_r("wctr_r"),
    irq_r("irq_r"),
    play_r("play_r"),
    req_r("req_r"),
    rctr_r("rctr_r"),
    //    rbank_ns("rbank_ns"),
    wctr_ns("wctr_ns"),
    irq_ns("irq_ns"),
    play_ns("play_ns"),
    req_ns("req_ns"),
    rctr_ns("rctr_ns"),
    rindex("rindex"),
    ready("ready"),
    write("write"),
    cmd_exe("cmd_exe"),
    start("start"),
    stop("stop"),
    clr("clr"),
    irqack("irqack"),
    cmd_err("cmd_err"),
    clr_err("clr_err"),
    cfg_err("cfg_err"),
    irq_err("irq_err")
    {
#ifdef control_unit_as_rtl
    SC_METHOD(control_logic_proc);
    sensitive << PADDR << PWDATA << PENABLE << PSEL << PWRITE << req_in;
    for(int i=0; i < AUDIOPORT_REGISTERS; ++i)
      sensitive << rbank_r[i];
    sensitive << wctr_r << irq_r << play_r << req_r << rctr_r;
    sensitive << rindex << ready << write << cmd_exe << start << stop << clr << irqack << cmd_err << clr_err << cfg_err << irq_err;
    
    SC_METHOD(control_regs_proc);
    sensitive << clk.pos() << rst_n.neg();

#else
      SC_CTHREAD(control_unit_proc, clk.pos());
      async_reset_signal_is(rst_n, false);
#endif
  }
    



};


#endif

#endif
