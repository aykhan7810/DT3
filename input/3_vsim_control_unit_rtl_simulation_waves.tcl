onerror {add wave -noupdate -divider {Wave setup error!}; resume}
configure wave -signalnamewidth 1
configure wave -datasetprefix 0
add wave -noupdate /audioport_pkg::mynumber
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clk
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rst_n
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PSEL
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PENABLE
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PWRITE
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PREADY
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PADDR
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PWDATA
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PRDATA
add wave -noupdate /control_unit_tb/DUT_INSTANCE/PSLVERR
add wave -noupdate /control_unit_tb/DUT_INSTANCE/req_in
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irq_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cfg_reg_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/level_reg_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/dsp_regs_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clr_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cfg_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/level_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/play_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/tick_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/audio0_out
add wave -noupdate /control_unit_tb/DUT_INSTANCE/audio1_out
add wave -noupdate -divider INTERNAL
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rindex
add wave -noupdate /control_unit_tb/DUT_INSTANCE/wctr_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rbank_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/play_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/rctr_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/req_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irq_r
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cmd_exe
add wave -noupdate /control_unit_tb/DUT_INSTANCE/start
add wave -noupdate /control_unit_tb/DUT_INSTANCE/stop
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clr
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irqack
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cmd_err
add wave -noupdate /control_unit_tb/DUT_INSTANCE/clr_err
add wave -noupdate /control_unit_tb/DUT_INSTANCE/cfg_err
add wave -noupdate /control_unit_tb/DUT_INSTANCE/irq_err

if  { [llength [find instances -bydu control_unit_svamod] ] > 0 } {
    add wave -noupdate -divider {BLACKBOX ASSERTIONS}
    add wave -nofilter Assertion /control_unit_tb/DUT_INSTANCE/CHECKER_MODULE/af_*
    add wave -noupdate -divider {WHITEBOX ASSERTIONS}
    add wave -nofilter Assertion /control_unit_tb/DUT_INSTANCE/CHECKER_MODULE/ar_*
    add wave -noupdate /audioport_util_pkg::assertions_failed
}

