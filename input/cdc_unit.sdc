######################################################################################
# cdc_unit.sdc: Timing Constraints File
#####################################################################################

# 1. Define clock period and clock edge times in ns

create_clock -name clk     -period 18.5  clk
create_clock -name mclk_in -period 54.25 mclk_in

set_clock_groups -asynchronous -name cdc_unit_clk_domains -group clk -group mclk_in

# 2. Define reset input delay relative to clock clk in ns

set_input_delay  -clock clk 5.0 rst_n

# 3. Define data input external delays relative to clock clk in ns

set_input_delay  -clock clk 2.3125 test_mode_in
set_input_delay  -clock clk 2.3125 dsp0_in
set_input_delay  -clock clk 2.3125 dsp1_in
set_input_delay  -clock clk 2.3125 tick_in
set_input_delay  -clock clk 2.3125 cfg_in
set_input_delay  -clock clk 2.3125 cfg_reg_in

# 4. Define output external delays relative to clock clk in ns

set_output_delay  -clock mclk_in 2.3125 dsp0_out
set_output_delay  -clock mclk_in 2.3125 dsp1_out
set_output_delay  -clock mclk_in 2.3125 tick_out
set_output_delay  -clock mclk_in 2.3125 cfg_out 
set_output_delay  -clock mclk_in 2.3125 cfg_reg_out


