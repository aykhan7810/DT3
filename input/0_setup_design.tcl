###################################################################
# Top-module selection
###################################################################

#set DESIGN_NAME "tlm_audioport"
set DESIGN_NAME "audioport"
#set DESIGN_NAME "control_unit"
#set DESIGN_NAME "i2s_unit"
#set DESIGN_NAME "cdc_unit"
#set DESIGN_NAME "dsp_unit"

if [info exists env(FORCED_DESIGN_NAME) ] {
    set DESIGN_NAME $env(FORCED_DESIGN_NAME)
}

source input/0_setup_${DESIGN_NAME}.tcl

###################################################################
# Settings common to all subprojects
###################################################################


# Override UVM_TESTNAME (e.g. from Makefile)
if [info exists env(UVM_TESTNAME) ] {
    set UVM_TESTNAME $env(UVM_TESTNAME)
}

# Define Verilog compiler macro that is used in source code to 
# to detect RTL simulation

if [info exists VLOG_RTL_OPTIONS] {
    set VLOG_RTL_OPTIONS         [concat $VLOG_RTL_OPTIONS         " -suppress 13314 -suppress 13233 +define+RTL_SIM" ]
}

set VCOM_RTL_OPTIONS "-2008"

if [info exists VLOG_SYSTEMC_OPTIONS] {
    set VLOG_SYSTEMC_OPTIONS     [concat $VLOG_SYSTEMC_OPTIONS     " -suppress 13314 -suppress 13233 +define+RTL_SIM" ]
}
if [info exists VLOG_MIXEDLANG_OPTIONS] {
    set VLOG_MIXEDLANG_OPTIONS   [concat $VLOG_MIXEDLANG_OPTIONS   " -suppress 13314 -suppress 13233 +define+RTL_SIM +define+SYSTEMC_DUT" ]
}
if [info exists VLOG_GATELEVEL_OPTIONS] {
    set VLOG_GATELEVEL_OPTIONS   [concat $VLOG_GATELEVEL_OPTIONS   " -suppress 13314 -suppress 13233 +define+GATELEVEL_SIM" ]
}

if [info exists VLOG_POSTLAYOUT_OPTIONS] {
    set VLOG_POSTLAYOUT_OPTIONS   [concat $VLOG_POSTLAYOUT_OPTIONS   " -suppress 13314 -suppress 13233 +define+POSTLAYOUT_SIM" ]
}

set XCELIUM_VLOG_RTL_OPTIONS       " -incdir input -incdir input/uvm -DEFINE RTL_SIM"
set XCELIUM_VLOG_MIXEDLANG_OPTIONS " -incdir input -incdir input/uvm -DEFINE RTL_SIM -DEFINE SYSTEMC_DUT" 

if [info exists VCS_VLOG_RTL_OPTIONS] {
    set VCS_VLOG_RTL_OPTIONS     [concat $VCS_VLOG_RTL_OPTIONS     " +define+RTL_SIM" ]
}


# Enable SAIF activity data recording
set RTL_POWER_ESTIMATION      1

# Set this to 0 when you have seen enough of the schematics 

set VSIM_SCHEMATIC 0

# Disable some commong warnings
if [info exists VSIM_GATELEVEL_OPTIONS] {
    set VSIM_GATELEVEL_OPTIONS  [concat $VSIM_GATELEVEL_OPTIONS " +nowarn3448" ]
}
if [info exists VSIM_POSTLAYOUT_OPTIONS] {
    set VSIM_POSTLAYOUT_OPTIONS [concat $VSIM_POSTLAYOUT_OPTIONS " +nowarn3448 +nowarn3438 +nowarnTSCALE" ]
}

# Assertion module bindings for the whole project are here:
set SVA_BIND_FILE "input/sva_bindings.svh"

# XML testplan file location
if { [file exists input/${DESIGN_NAME}_testplan.xml ] == 1} {
    set VSIM_TESTPLAN input/${DESIGN_NAME}_testplan.xml
}

# Testplan generation parameters
if { [info exists XML2UCDB_OPTIONS] == 0 || $XML2UCDB_OPTIONS == "" } {
    set XML2UCDB_OPTIONS "-GDESIGN_NAME=${DESIGN_NAME} -GSIM_PREFIX=/${DESIGN_NAME}_tb/DUT_INSTANCE -GFORMAL_PREFIX=/${DESIGN_NAME}"
}

# Disable SDC file if it does not exits

if { [info exists SDC_FILE ] } {
    if { [file exists $SDC_FILE ] == 0} {
	unset SDC_FILE
    }
}

# Filters for selecting assertions to report in Questa Formal
if { [info exists QFORMAL_BB_PROPERTIES] == 0 || $QFORMAL_BB_PROPERTIES == "" } {
    set QFORMAL_BB_PROPERTIES "CHECKER_MODULE.af_*"
}
if { [info exists QFORMAL_WB_PROPERTIES] == 0 || $QFORMAL_WB_PROPERTIES == "" } {
    set QFORMAL_WB_PROPERTIES "CHECKER_MODULE.ar_*"
}

set QAUTOCHECK_DISABLE_CHECKS { CASE_DEFAULT }

# Make Jasper FV to run longer
set JASPER_TRACE_LENGTH 3000

# Some Design Compiler settings

set DC_SUPPRESS_MESSAGES { "UID-401" "UID-348" "TEST-130" "TIM-104" "TIM-134" "TIM-179" "VER-26" "VO-4" "VHD-4"}


###################################################################
# Select SDF backannotation delay types (MIN, TYP, MAX)
###################################################################

set GATELEVEL_SDF  MAX
set POSTLAYOUT_SDF MAX
