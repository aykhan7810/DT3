######################################################################################################
#
#  Common Settings
#
######################################################################################################

# Design source code
define_hls_module dsp_unit [list $LAUNCH_DIR/input/dsp_unit.cpp]

# I/O configurations (PIN interfaces only)
define_io_config dsp_unit PIN

# Behavioral simulation configuration for simulation from Stratus
define_sim_config B -io_config PIN -argv "-run stratus_BEH -output ${LAUNCH_DIR}/output" { dsp_unit BEH }

######################################################################################################
#
#  UNCONSTRAINED_CFG
#
######################################################################################################

if {1} {

# HLS configuration
define_hls_config dsp_unit UNCONSTRAINED_CFG "--flatten_arrays=all" -uarch_tcl UNCONSTRAINED_CFG_settings

# Micro-architecture directive TCL code to be passed to 'define_hls_config' with -uarch_tcl
proc UNCONSTRAINED_CFG_settings { } {
    define_protocol  -name "RESET_REGION"  [ find -region "RESET_REGION"]
    define_protocol  -name "INPUT_REGION"  [ find -region "INPUT_REGION"]
    define_protocol  -name "OUTPUT_REGION"  [ find -region "OUTPUT_REGION"]
    assume_stable    -name "stable_dsp_regs" [find -region "PROCESSING_REGION"] "dsp_proc/dsp_regs_r"
}

# RTL simulation configurations for simulation from Stratus
define_sim_config UNCONSTRAINED_CFG_RTL_V -argv "-run stratus_UNCONSTRAINED_CFG -output ${LAUNCH_DIR}/output" \
    -verilog_simulator ${STRATUS_VERILOG_SIMULATOR} { dsp_unit RTL_V UNCONSTRAINED_CFG }

# Logic synthesis configuration
define_logic_synthesis_config UNCONSTRAINED_CFG_LOGICSYN { dsp_unit UNCONSTRAINED_CFG }  -options {BDW_LS_NOGATES 1}

}

######################################################################################################
#
#  ASAP_CFG
#
######################################################################################################

if {1} {

define_hls_config dsp_unit ASAP_CFG "--flatten_arrays=all --unroll_loops=on --sched_asap=on" -uarch_tcl ASAP_CFG_settings

proc ASAP_CFG_settings { } {
   define_protocol  -name "RESET_REGION"    [ find -region "RESET_REGION"]
   define_protocol  -name "INPUT_REGION"    [ find -region "INPUT_REGION"]
   define_protocol  -name "OUTPUT_REGION"   [ find -region "OUTPUT_REGION"]
   assume_stable    -name "stable_dsp_regs" [find -region "PROCESSING_REGION"] "dsp_proc/dsp_regs_r"
}

define_logic_synthesis_config ASAP_CFG_LOGICSYN { dsp_unit ASAP_CFG }  -options {BDW_LS_NOGATES 1}

define_sim_config ASAP_CFG_RTL_V -argv "-run stratus_ASAP_CFG -output ${LAUNCH_DIR}/output" \
    -verilog_simulator ${STRATUS_VERILOG_SIMULATOR} { dsp_unit RTL_V ASAP_CFG }

}

######################################################################################################
#
#  OPTIMIZED_CFG
#
######################################################################################################

if {1} {

define_hls_config dsp_unit OPTIMIZED_CFG "--flatten_arrays=all" -uarch_tcl OPTIMIZED_CFG_settings

proc OPTIMIZED_CFG_settings { } {
    define_protocol  -name "RESET_REGION"  [ find -region "RESET_REGION"]
    define_protocol  -name "INPUT_REGION"  [ find -region "INPUT_REGION"]
    define_protocol  -name "OUTPUT_REGION"  [ find -region "OUTPUT_REGION"]
    assume_stable    -name "stable_dsp_regs" [find -region "PROCESSING_REGION"] "dsp_proc/dsp_regs_r"
    constrain_latency -name "PROCESSING_REGION_LAT"  -min_lat 0 -max_lat 100 [find -region "PROCESSING_REGION"]
#
# Loop unrolling examples:
#
#    1. Unroll one loop
#    unroll_loops -type ON  -name "CLEAR_LOOP"  [ find -loop "CLEAR_LOOP"]
#
#    2. Unroll loop and all inner loops
#    unroll_loops -type ALL -name "CLEAR_LOOP"  [ find -loop "CLEAR_LOOP"]
#
#    3. Unroll loop partially two times (two iterations moved doutside loop)
#    unroll_loops -type COMPLETE -count 2  -name "CLEAR_LOOP"  [ find -loop "CLEAR_LOOP"]
#
#    4. Unroll loop partially two times (whole loop body is replicated twice, iteration count halved)
#    unroll_loops -type CONSERVATIVE -count 2    -name "ACCU_LOOP"       [ find -loop "ACCU_LOOP"]
#    constrain_latency -name "ACCU_LOOP_LAT" -max_lat 2 [find -loop "ACCU_LOOP"]
}

define_logic_synthesis_config OPTIMIZED_CFG_LOGICSYN { dsp_unit OPTIMIZED_CFG }  -options {BDW_LS_NOGATES 1}

define_sim_config OPTIMIZED_CFG_RTL_V -argv "-run stratus_OPTIMIZED_CFG -output ${LAUNCH_DIR}/output" \
    -verilog_simulator ${STRATUS_VERILOG_SIMULATOR} { dsp_unit RTL_V OPTIMIZED_CFG }

}








