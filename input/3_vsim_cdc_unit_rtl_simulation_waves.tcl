onerror {add wave -noupdate -divider {Wave setup error!}; resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /audioport_pkg::mynumber
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/clk
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/rst_n
add wave -noupdate /cdc_unit_tb/DUT_INSTANCE/mclk_in
add wave -noupdate -expand -group testmux /cdc_unit_tb/DUT_INSTANCE/test_mode_in
add wave -noupdate -expand -group testmux /cdc_unit_tb/DUT_INSTANCE/mclk
add wave -noupdate -expand -group testmux /cdc_unit_tb/DUT_INSTANCE/mrst_n
add wave -noupdate -expand -group reset_sync /cdc_unit_tb/DUT_INSTANCE/srst_n
add wave -noupdate -expand -group play_sync /cdc_unit_tb/DUT_INSTANCE/play_in
add wave -noupdate -expand -group play_sync /cdc_unit_tb/DUT_INSTANCE/play_out
add wave -noupdate -expand -group req_sync /cdc_unit_tb/DUT_INSTANCE/req_in
add wave -noupdate -expand -group req_sync /cdc_unit_tb/DUT_INSTANCE/req_out
add wave -noupdate -expand -group cfg_sync /cdc_unit_tb/DUT_INSTANCE/cfg_in
add wave -noupdate -expand -group cfg_sync /cdc_unit_tb/DUT_INSTANCE/cfg_reg_in
add wave -noupdate -expand -group cfg_sync /cdc_unit_tb/DUT_INSTANCE/cfg_out
add wave -noupdate -expand -group cfg_sync /cdc_unit_tb/DUT_INSTANCE/cfg_reg_out
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/tick_in
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/dsp0_in
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/dsp1_in
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/tick_out
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/dsp0_out
add wave -noupdate -expand -group audio_sync /cdc_unit_tb/DUT_INSTANCE/dsp1_out
add wave -noupdate -format Analog-Step -height 84 -max 400 /cdc_unit_tb/TEST/tmaxlatency

configure wave -signalnamewidth 1
configure wave -datasetprefix 0

