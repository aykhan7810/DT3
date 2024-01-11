###################################################################
# cdc_unit environment setup
###################################################################

set DESIGN_NAME "cdc_unit"

set DESIGN_FILES {  "input/apb_pkg.sv" \
		    "input/audioport_pkg.sv" \
		    "input/audioport_util_pkg.sv" \
                 }

set RTL_FILES    { "input/cdc_unit.sv" }

set SVA_FILES    { "input/cdc_unit_svamod.sv" }

set TESTBENCH_FILES { "input/cdc_unit_test.sv" \
		      "input/cdc_unit_tb.sv" }

set RTL_LANGUAGE "SystemVerilog"

set SYSTEMC_SOURCE_FILES    "input/cdc_unit.cpp"
set SYSTEMC_HEADER_FILES    "input/cdc_unit.h"
set SYSTEMC_TESTBENCH_FILES ""
set SYSTEMC_MODULES          {  "cdc_unit"  }

###################################################################
# Timing Constraints
###################################################################

set SDC_FILE              input/${DESIGN_NAME}.sdc

set CLOCK_NAMES           {"clk"   "mclk_in" }
set CLOCK_PERIODS         { 17.5      54.25  }
set CLOCK_UNCERTAINTIES   { 0.0         0.0  }
set CLOCK_LATENCIES       { 0.0         0.0  }
set INPUT_DELAYS          {   0           0  }
set OUTPUT_DELAYS         {   0           0  }
set OUTPUT_LOAD           0.01
set RESET_NAMES           { "rst_n" "mrst_n" }
set RESET_LEVELS          { 0             0  }
set RESET_STYLES          {  "async" "async" }

set CLOCK_DOMAIN_PORTS    { { test_mode_in play_in tick_in dsp0_in dsp1_in cfg_in cfg_reg_in req_out rst_n } \
			    { play_out tick_out dsp0_out dsp1_out cfg_out cfg_reg_out req_in mrst_n} }

###################################################################
# Settings for simulation scripts
###################################################################

set VSIM_RTL_WAVES             "input/3_vsim_cdc_unit_rtl_simulation_waves.tcl"
set VSIM_MIXEDLANG_WAVES       "input/3_vsim_cdc_unit_rtl_simulation_waves.tcl"

set RTL_SIMULATION_TIME        "-all"
set GATELEVEL_SIMULATION_TIME  "-all"

# Define wilcard pattern that match sync flip-flop names
#set VSIM_DISABLE_TIMINGCHECKS { "*ff1*" "*ff2*" }

###################################################################
# Settings for static verification scripts
###################################################################

set QUESTA_INIT_FILE  "input/rst.questa_init"
set QUESTA_DIRECTIVES "input/cdc_unit.questa_dir.tcl"

###################################################################
# Synthesis settings
###################################################################

# Constraints file that contains Design Compiler commands
set SYNTHESIS_CONSTRAINTS_FILE    "input/cdc_unit.syn_constraints.tcl"

# Enable reset removal and recovery checks and hold fixing
set SYNTHESIS_RECREM_ARCS  1
set SYNTHESIS_FIX_HOLD     1



