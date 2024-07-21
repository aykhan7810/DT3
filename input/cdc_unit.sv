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
   logic test_mode_mclk, test_mode_mrst_n;
   logic play_in_reg, cfg_in_reg, tick_in_reg;
   logic [31:0] cfg_reg_in_reg;
   logic [23:0] dsp0_in_reg, dsp1_in_reg;
   logic req_in_reg;
   
   logic tx_en, req, sack;
   logic sreq, ack;
/*
   // Register inputs
   cdc_reg #(1) u_play_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(play_in),
      .out(play_in_reg)
   );

   cdc_reg #(1) u_cfg_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(cfg_in),
      .out(cfg_in_reg)
   );

   cdc_reg #(32) u_cfg_reg_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(cfg_reg_in),
      .out(cfg_reg_in_reg)
   );

   cdc_reg #(1) u_tick_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(tick_in),
      .out(tick_in_reg)
   );

   cdc_reg #(24) u_dsp0_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(dsp0_in),
      .out(dsp0_in_reg)
   );

   cdc_reg #(24) u_dsp1_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(dsp1_in),
      .out(dsp1_in_reg)
   );

   cdc_reg #(1) u_req_in_reg (
      .clk(clk),
      .rst_n(rst_n),
      .in(req_in),
      .out(req_in_reg)
   );
*/   
   testmux u_testmux (
      .clk(clk),
      .rst_n(rst_n),
      .test_mode_in(test_mode_in),
      .mclk_in(mclk_in),
      .mclk(test_mode_mclk),
      .mrst_n(test_mode_mrst_n)
   );
   assign mclk = test_mode_mclk;
   assign mrst_n = test_mode_mrst_n;
   
   // Reset synchronization
   reset_sync u_reset_sync (
      .clk(mclk),
      .rst_n(rst_n),
      .mrst_n(srst_n)
   );

   // Play synchronization
   bit_sync u_play_sync (
      .clk(mclk),
      .rst_n(srst_n),
      .data_in(play_in),
      .data_out(play_out)
   );
   
   // Request synchronization
   pulse_sync pulse_req_sync (
      .clk(clk),
      .rst_n(rst_n),
      .data_in(req_in),
      .data_out(req_out)
   );
   
/*   // Synchronizers for req and ack signals
   bit_sync u_req_sync (
      .clk(mclk),
      .rst_n(srst_n),
      .data_in(req),
      .data_out(sreq)
   );

   bit_sync u_ack_sync (
      .clk(clk),
      .rst_n(rst_n),
      .data_in(ack),
      .data_out(sack)
   );
*/
   // Configuration synchronization
   data_sync #(.DATABITS(32)) u_cfg_sync (
      .clk(mclk),
      .rst_n(srst_n),
      .en_in(cfg_in),
      .data_in(cfg_reg_in),
      .en_out(cfg_out),
      .data_out(cfg_reg_out)
   );

   // Audio data synchronization
   data_sync #(.DATABITS(24)) u_dsp_sync (
      .clk(mclk),
      .rst_n(srst_n),
      .en_in(tick_in),
      .data_in({dsp1_in, dsp0_in}),
      .en_out(tick_out),
      .data_out({dsp1_out, dsp0_out})
   );
   
endmodule
/*
// TX FSM
   typedef enum logic [1:0] {TX_IDLE, TX_REQ, TX_ACK} tx_state_t;
   tx_state_t tx_state_r, tx_state_ns;

   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n)
         tx_state_r <= TX_IDLE;
      else
         tx_state_r <= tx_state_ns;
   end

   always_comb begin
      tx_state_ns = tx_state_r;
      tx_en = 1'b0;
      req = 1'b0;

      case (tx_state_r)
         TX_IDLE: if (tick_in_reg && !sack) begin
            tx_en = 1'b1;
            tx_state_ns = TX_REQ;
         end
         TX_REQ: begin
            req = 1'b1;
            if (sack) begin
               tx_state_ns = TX_ACK;
            end
         end
         TX_ACK: begin
            if (!sack)
               tx_state_ns = TX_IDLE;
         end
      endcase
   end

   // RX FSM
   typedef enum logic [1:0] {RX_IDLE, RX_ACK} rx_state_t;
   rx_state_t rx_state_r, rx_state_ns;

   always_ff @(posedge mclk or negedge srst_n) begin
      if (!srst_n)
         rx_state_r <= RX_IDLE;
      else
         rx_state_r <= rx_state_ns;
   end

   always_comb begin
      rx_state_ns = rx_state_r;
      ack = 1'b0;
      tick_out = 1'b0;

      case (rx_state_r)
         RX_IDLE: if (sreq) begin
            ack = 1'b1;
            rx_state_ns = RX_ACK;
         end
         RX_ACK: begin
            tick_out = 1'b1;
            if (!sreq)
               rx_state_ns = RX_IDLE;
         end
      endcase
   end
/*
module cdc_reg #(parameter WIDTH = 1)
  (
   	input logic clk,
   	input logic rst_n,
   	input logic [WIDTH-1:0] in,
   	output logic [WIDTH-1:0] out
  );

   	always_ff @(posedge clk or negedge rst_n) begin
      	if (!rst_n) begin
         	out <= {WIDTH{1'b0}};
      	end else begin
         	out <= in;
      	end
   	end

endmodule */

module testmux
  (
  	input logic clk,
   	input logic rst_n,
   	input logic test_mode_in,
   	input logic mclk_in,
   	output logic mclk,
   	output logic mrst_n
  );
  
	always_comb 
	begin : test_mux
		if (test_mode_in) begin
			mclk = clk;
         	mrst_n = rst_n;
      	end else begin
         	mclk = mclk_in;
         	mrst_n = 1'b1;
      	end
	end : test_mux
   
endmodule


module reset_sync
    (
    input logic clk,
   	input logic rst_n,
   	output logic mrst_n
   	);
   	
	logic rsync_ff1, rsync_ff2;

   	always_ff @(posedge clk or negedge rst_n) begin
      	if (!rst_n) begin
        	rsync_ff1 <= '0;
         	rsync_ff2 <= '0;
      	end else begin
         	rsync_ff1 <= '1;
         	rsync_ff2 <= rsync_ff1;
      	end
   	end

   	assign mrst_n = rsync_ff2;

endmodule


module bit_sync
   (
   input logic clk,
   input logic rst_n,
   input logic data_in,
   output logic data_out
   );

   logic bsync_ff1, bsync_ff2;
   
   always_ff @(posedge clk or negedge rst_n) begin
   		if (!rst_n) begin
        	bsync_ff1 <= '0;
         	bsync_ff2 <= '0;
      	end else begin
         	bsync_ff1 <= data_in;
         	bsync_ff2 <= bsync_ff1;
      	end
   end

   assign data_out = bsync_ff2;

endmodule

module pulse_sync
   (
   input logic clk,
   input logic rst_n,
   input logic data_in,
   output logic data_out
   );

   logic psync_ff1, psync_ff2, pulse;

   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         psync_ff1 <= '0;
         psync_ff2 <= '0;
         pulse <= '0;
      end else begin
         psync_ff1 <= data_in;
         psync_ff2 <= psync_ff1;
         pulse <= psync_ff1 & ~psync_ff2;
      end
   end

   assign data_out = pulse;

endmodule

module data_sync #(DATABITS = 8) 
   (
/*   input logic clk,
   input logic enable,
   input logic [DATABITS-1:0] in,
   output logic [DATABITS-1:0] out
   );

   logic [DATABITS-1:0] dsync_ff1, dsync_ff2;

   always_ff @(posedge clk) begin
      if (enable) begin
         dsync_ff1 <= in;
         dsync_ff2 <= dsync_ff1;
      end
   end

   assign out = dsync_ff2;
*/
	
   input logic clk,
   input logic rst_n,
   input logic en_in,
   input logic [2*DATABITS-1:0] data_in,
   //input logic [31:0] data_in,
   output logic en_out,
   output logic [2*DATABITS-1:0] data_out
   //output logic [31:0] data_out
   );

   logic [2*DATABITS-1:0] dsync_ff1, dsync_ff2;
   logic en_ff1, en_ff2;

   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         dsync_ff1 <= {2*(DATABITS){1'b0}};
         dsync_ff2 <= {2*(DATABITS){1'b0}};
         en_ff1 <= '0;
         en_ff2 <= '0;
      end else begin
         if (en_in) begin
            dsync_ff1 <= data_in;
            en_ff1 <= en_in;
         end
         dsync_ff2 <= dsync_ff1;
         en_ff2 <= en_ff1;
      end
   end

   assign data_out = dsync_ff2;
   assign en_out = en_ff2;
   
endmodule



