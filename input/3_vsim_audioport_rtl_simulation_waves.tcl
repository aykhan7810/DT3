###########################################################################
# Wave window setup script for QuestaSim / audioport
###########################################################################

onerror {add wave -noupdate -divider {Wave setup error!}; resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /audioport_pkg::mynumber
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/clk
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/rst_n
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/mclk
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/mclk_mux
add wave -noupdate  -group Clocks /audioport_tb/DUT_INSTANCE/mrst_n

###########################################################################
# Test ports
###########################################################################

add wave -noupdate -divider Test
add wave -noupdate -group Test /audioport_tb/DUT_INSTANCE/test_mode_in
add wave -noupdate -group Test /audioport_tb/DUT_INSTANCE/scan_en_in

###########################################################################
# APB UVM transactions
###########################################################################

add wave -noupdate -divider {APB}

if { $UVM_TESTBENCH == 1 } {
    if { $UVM_TESTNAME == "apb_test" } {
	add wave -noupdate -group APB /uvm_root/uvm_test_top/m_env/m_agent/m_sequencer/seq
    }
    if { $UVM_TESTNAME == "control_unit_uvm_test" } {
	add wave -noupdate -group APB /uvm_root/uvm_test_top/m_env/m_control_unit_agent/m_sequencer/seq
    }
    if { $UVM_TESTNAME == "audioport_uvm_test" } {
	add wave -noupdate -group APB /uvm_root/uvm_test_top/m_env/m_control_unit_agent/m_sequencer/main_seq
    }
}

###########################################################################
# APB ports
###########################################################################

add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PSEL
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PENABLE
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PWRITE
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PADDR
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PWDATA
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PRDATA
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PREADY
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PSLVERR
add wave -noupdate -group APB /audioport_tb/DUT_INSTANCE/irq_out
if { $UVM_TESTBENCH == 1 } {
    if { $UVM_TESTNAME == "control_unit_uvm_test" } {
	add wave uvm_root/uvm_test_top/m_env/m_control_unit_agent/m_irq_event
    }
    if { $UVM_TESTNAME == "audioport_uvm_test" } {
	add wave uvm_root/uvm_test_top/m_env/m_control_unit_agent/m_irq_event
    }
}

###########################################################################
# I2S ports
###########################################################################

add wave -noupdate -divider I2S

add wave -noupdate -expand -group I2S /audioport_tb/DUT_INSTANCE/ws_out
add wave -noupdate -expand -group I2S /audioport_tb/DUT_INSTANCE/sck_out
add wave -noupdate -expand -group I2S /audioport_tb/DUT_INSTANCE/sdo_out

###########################################################################
# Internal / clk Domain
###########################################################################

add wave -noupdate -divider {INTERNAL (clk)}

if { [info exists VSIM_VISUALIZER ] } {
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /audioport_tb/DUT_INSTANCE/audio0
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /audioport_tb/DUT_INSTANCE/audio1
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /audioport_tb/DUT_INSTANCE/dsp0
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /audioport_tb/DUT_INSTANCE/dsp1
} else {
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /audioport_tb/DUT_INSTANCE/audio0
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /audioport_tb/DUT_INSTANCE/audio1
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /audioport_tb/DUT_INSTANCE/dsp0
    add wave -noupdate -expand -group AUDIO -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /audioport_tb/DUT_INSTANCE/dsp1
}

add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/play
add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/tick
add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/dsp_tick
add wave -noupdate  -group AUDIO /audioport_tb/DUT_INSTANCE/req

add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/cfg
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/cfg_reg
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/level_reg
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/dsp_regs
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/level
add wave -noupdate  -group CONTROL /audioport_tb/DUT_INSTANCE/clr

###########################################################################
# Internal / mclk Domain
###########################################################################

add wave -noupdate -divider {INTERNAL (mclk)}

add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mplay
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mtick
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mreq
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mcfg
add wave -noupdate  -group {mclk DOMAIN} /audioport_tb/DUT_INSTANCE/mcfg_reg

if { [info exists VSIM_VISUALIZER ] } {
    add wave -noupdate -expand -group {mclk DOMAIN} -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /audioport_tb/DUT_INSTANCE/mdsp0
    add wave -noupdate -expand -group {mclk DOMAIN} -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /audioport_tb/DUT_INSTANCE/mdsp1
} else {
    add wave -noupdate -expand -group {mclk DOMAIN} -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /audioport_tb/DUT_INSTANCE/mdsp0
    add wave -noupdate -expand -group {mclk DOMAIN} -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /audioport_tb/DUT_INSTANCE/mdsp1
}

###########################################################################
# audioport_uvm_test related
###########################################################################

if { $UVM_TESTBENCH == 1 && $UVM_TESTNAME == "audioport_uvm_test"} {

    add wave -noupdate -divider {DUT-vs-REF}
    if { [info exists VSIM_VISUALIZER ] } {
	add wave -group DUT -radix decimal /audioport_tb/DUT_INSTANCE/audio0
	add wave -group DUT -radix decimal /audioport_tb/DUT_INSTANCE/audio1
	add wave -noupdate -group DUT -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement {/audioport_tb/i2s/monitor/audio_out[1]}
	add wave -noupdate -group DUT -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement {/audioport_tb/i2s/monitor/audio_out[0]}

	add wave -noupdate -group REF -radix decimal -representation twoscomplement /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/audio0
	add wave -noupdate -group REF -radix decimal -representation twoscomplement /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/audio1
	add wave -noupdate -group REF -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/dsp0
	add wave -noupdate -group REF -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal -representation twoscomplement /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/dsp1
    } else {
	add wave -group DUT -radix decimal /audioport_tb/DUT_INSTANCE/audio0
	add wave -group DUT -radix decimal /audioport_tb/DUT_INSTANCE/audio1
	add wave -noupdate -group DUT -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal {/audioport_tb/i2s/monitor/audio_out[1]}
	add wave -noupdate -group DUT -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal {/audioport_tb/i2s/monitor/audio_out[0]}

	add wave -noupdate -group REF -radix decimal /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/audio0
	add wave -noupdate -group REF -radix decimal /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/audio1
	add wave -noupdate -group REF -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/dsp0
	add wave -noupdate -group REF -format Analog-Step -height 84 -max 8388607 -min -8388607 -radix decimal /uvm_root/uvm_test_top/m_env/m_scoreboard/m_predictor/dsp1
    }
}



configure wave -signalnamewidth 1
configure wave -datasetprefix 0
