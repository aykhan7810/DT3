onerror {resume}
quietly WaveActivateNextPane {} 0
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clk
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/rst_n
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_tb_inst/sample_number
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/cfg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clr_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/level_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/cfg_reg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/level_reg_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp_regs_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio0_in
add wave -noupdate -format Analog-Step -height 84 -max 7969177.0 -min -4194304.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio0_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio1_in
add wave -noupdate -format Analog-Step -height 84 -max 7969177.0 -min -4194304.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/audio1_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/valid_out
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp0_out
add wave -noupdate -format Analog-Step -height 84 -max 7969175.9999999991 -min -6789785.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp0_out
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp1_out
add wave -noupdate -format Analog-Step -height 84 -max 7969176.0 -min -6827082.0 -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_inst/dsp1_out
add wave -noupdate -divider {Latency Check:}
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/clk
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/tick_in
add wave -noupdate /sc_main/dsp_unit_top_inst/dsp_unit_inst/valid_out
add wave -noupdate -radix decimal /sc_main/dsp_unit_top_inst/dsp_unit_tb_inst/latency
add wave -noupdate -format Analog-Step -max 300.0 /sc_main/dsp_unit_top_inst/dsp_unit_tb_inst/latency

configure wave -signalnamewidth 1
configure wave -datasetprefix 0
