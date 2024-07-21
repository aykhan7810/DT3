#
# i2s_unit.sdc: Timing Constraints File
#

# 1. Define clock period and clock edge times in ns

create_clock -name clk -period 18.5 clk
set_ideal_network clk
create_clock -name mclk -period 54.253472222 mclk
set_ideal_network mclk
set_clock_groups -asynchronous -name cdc_unit_clk_domains -group clk -group mclk

# 2. Define reset input timing wrt clock in ns

set_input_delay  -clock clk 5.0 rst_n

# 3. Define input external delays (arrival times) wrt clock in ns

set_input_delay  -clock clk 2.0 [all_inputs]

# 4. Define output external delays (setup times) wrt clock in ns

set_output_delay  -clock clk 2.0 [all_outputs]
