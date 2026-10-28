import OCaml.Vm.Sim.CountedEntry
import OCaml.Vm.Sim.OutListF1Runtime
import OCaml.Vm.Sim.PrimOpenOutReturns

/-! Focused custom physical/context audits; full OCaml.Audit stays at the lead gate. -/

#print axioms OCaml.Vm.Gc.CustomCallPins.frame
#print axioms OCaml.Vm.Gc.CustomCallPins.startup
#print axioms OCaml.Vm.Gc.CustomCallRead.bounds
#print axioms OCaml.Vm.Gc.CustomCallPins.domain
#print axioms OCaml.Vm.Gc.CustomCallPins.table
#print axioms OCaml.Vm.Gc.resource_targets_below_one
#print axioms OCaml.Vm.Gc.resource_target_six
#print axioms OCaml.Vm.Gc.customTableWord_frame
#print axioms OCaml.Vm.Gc.CustomTableShape.frame
#print axioms OCaml.Vm.Gc.PhysicalCustoms.unique
#print axioms OCaml.Vm.Gc.PhysicalCustoms.frame
#print axioms OCaml.Vm.Gc.PhysicalCustoms.startup
#print axioms OCaml.Vm.Gc.physicalAccounting
#print axioms OCaml.Vm.Gc.PhysicalCustoms.quietTable
#print axioms OCaml.Vm.Gc.PhysicalCustoms.not_full
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_custom_table_end
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_custom_table_threshold
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_custom_table_limit
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_custom_table_size
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_custom_table_reserve
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_minor_heap_wsz
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_stat_heap_wsz
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_extra_heap_resources_minor
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_caml_custom_minor_max_bsz
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_caml_custom_minor_ratio
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_caml_custom_major_ratio
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_lambda
#print axioms OCaml.Vm.Boot.WhileMinRuntime.read_caml_extra_heap_resources
#print axioms OCaml.Vm.Gc.CustomCallRead.not_state
#print axioms OCaml.Vm.Gc.CustomCallRead.notFoot
#print axioms OCaml.Vm.Gc.CustomCallRead.outside_record
#print axioms OCaml.Vm.Gc.customCall_in_kept
#print axioms OCaml.Vm.Sim.f1_physical_counted_entry
#print axioms OCaml.Vm.Sim.whileMin_physical_counted_entry
#print axioms OCaml.Vm.Gc.f1_core
#print axioms OCaml.Vm.Gc.f1Pins_of
#print axioms OCaml.Vm.Gc.f1Runtime_of
#print axioms OCaml.Vm.Gc.f1_domainField
#print axioms OCaml.Vm.Gc.f1_nursery
#print axioms OCaml.Vm.Gc.stackWindow_apart
#print axioms OCaml.Vm.Gc.domainField_apart
#print axioms OCaml.Vm.Gc.QuietCustomTable.not_full
#print axioms OCaml.Vm.Primitives.Channel.ml_open_descriptor
#print axioms OCaml.Vm.Primitives.Channel.out_nursery
#print axioms OCaml.Vm.Sim.OutListWalk.walk_enter
#print axioms OCaml.Vm.Sim.OutListWalk.walk_listed
#print axioms OCaml.Vm.Sim.OutListWalk.walk_start
#print axioms OCaml.Vm.Sim.OutListWalk.f1_outList_entry
#print axioms OCaml.Vm.Sim.OutListWalk.outList_f1_restore
#print axioms OCaml.Vm.Sim.f1_entryStable
#print axioms OCaml.Vm.Sim.counted_entry_of_custom

#print axioms OCaml.Vm.Gc.PhysicalCustoms.table_bounds

#print axioms OCaml.Vm.Primitives.Channel.OpenedOut.context
#print axioms OCaml.Vm.Sim.OutListWalk.OutListReturned.context

#print axioms OCaml.Vm.Gc.custom_resource_parameters

#print axioms OCaml.Vm.Gc.CallerApart.congr
#print axioms OCaml.Vm.Gc.nullCustom_caller
#print axioms OCaml.Vm.Gc.physical_footprint
#print axioms OCaml.Vm.Gc.physical_complete
#print axioms OCaml.Vm.Gc.physical_apart
#print axioms OCaml.Vm.Gc.physical_frame

#print axioms OCaml.Vm.Sim.EntryFrame.accountingFrame
