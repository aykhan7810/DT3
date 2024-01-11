`include "audioport.svh"

import audioport_pkg::*;

module cdc_unit
  (
   input logic 	       clk,
   input logic 	       rst_n,
   input logic 	       test_mode_in,
   input logic [23:0]  dsp0_in,
   input logic [23:0]  dsp1_in,
   input logic 	       play_in,
   input logic 	       tick_in,
   input logic 	       cfg_in,
   input logic [31:0]  cfg_reg_in,
   output logic        req_out,

   input logic 	       mclk_in,
   output logic        mclk,
   output logic        mrst_n,
   output logic [23:0] dsp0_out,
   output logic [23:0] dsp1_out, 
   output logic        play_out,
   output logic        tick_out,
   output logic        cfg_out,
   output logic [31:0] cfg_reg_out,
   input logic 	       req_in		
   );
   
   logic 	       srst_n;
   
endmodule


module testmux
  (
   );

endmodule


module reset_sync
    (
   );

endmodule


module bit_sync
   (
    );

endmodule


module pulse_sync
   (
    );

endmodule


module data_sync #(DATABITS = 8) 
   (
    );

endmodule




