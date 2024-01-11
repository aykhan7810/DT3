if { $EDA_TOOL == "Design-Compiler" } {
    set_ungroup [get_cells * ] false
}

if { $EDA_TOOL == "Genus" } {
    set_db [get_db design:cdc_unit hinsts -depth 1 * -if {.obj_type == hinst }] .ungroup_ok false
}
