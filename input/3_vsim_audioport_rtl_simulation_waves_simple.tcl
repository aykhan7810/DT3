###########################################################################
# Wave window setup script for QuestaSim / audioport
###########################################################################

onerror {add wave -noupdate -divider {Wave setup error!}; resume}
quietly WaveActivateNextPane {} 0

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
# APB ports
###########################################################################

add wave -noupdate -divider {APB}

add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PSEL
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PENABLE
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PWRITE
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PADDR
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PWDATA
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PRDATA
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PREADY
add wave -noupdate -expand -group APB /audioport_tb/DUT_INSTANCE/PSLVERR
add wave -noupdate -group APB /audioport_tb/DUT_INSTANCE/irq_out

###########################################################################
# I2S ports
###########################################################################

add wave -noupdate -divider I2S

add wave -noupdate -expand -group I2S /audioport_tb/DUT_INSTANCE/ws_out
add wave -noupdate -expand -group I2S /audioport_tb/DUT_INSTANCE/sck_out
add wave -noupdate -expand -group I2S /audioport_tb/DUT_INSTANCE/sdo_out


###########################################################################
# Internal
###########################################################################

add wave -noupdate -divider Internal

add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/tick
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/play
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/cfg
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/level
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/clr
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/audio0
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/audio1
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/cfg_reg
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/level_reg
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/dsp_regs
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/dsp0
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/dsp1
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/dsp_tick
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mclk_mux
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mrst_n
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mtick
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mplay
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mreq
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mcfg
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mcfg_reg
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mdsp0
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/mdsp1
add wave -noupdate -group Internal /audioport_tb/DUT_INSTANCE/req

configure wave -signalnamewidth 1
configure wave -datasetprefix 0
