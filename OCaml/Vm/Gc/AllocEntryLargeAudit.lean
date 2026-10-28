import OCaml.Vm.Gc.AllocEntryLarge

/-! Focused audit for original-caller bounded least-large wrapper allocation.
Full OCaml.Audit remains the lead gate. -/

#print axioms OCaml.Vm.Gc.AllocEntryLarge.freeRegs_request
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.native_bounds
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.prologue_inside
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.prologue_read
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.prepared_least
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.prepared_header
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.prepared_representation
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.entered_least
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.entered_header
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.entry_input
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.result_header
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.header_nat
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.header_write
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.static_out
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.free_inside
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.prefix_inside
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.free_outside
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.header_inside
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.initialized_read
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.ready_read
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.saved_tag
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.color
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.continuation
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.large_input
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.wrapper_conditions
#print axioms OCaml.Vm.Gc.AllocEntryLarge.finish_memory
#print axioms OCaml.Vm.Gc.AllocEntryLarge.finish_read
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.finished_representation
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.wrapper_header
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.wrapper_log
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.effect_inside
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Input.returned
#print axioms OCaml.Vm.Gc.AllocEntryLarge.allocate
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Post.logWindows
#print axioms OCaml.Vm.Gc.AllocEntryLarge.Post.live

#print axioms OCaml.Vm.Gc.logInW_transport
#print axioms OCaml.Vm.Gc.logInW_join
#print axioms OCaml.Vm.Gc.BfShape.BoundedSmallRepresentation.of_reads
#print axioms OCaml.Vm.Gc.AllocLarge.Input.finish
#print axioms OCaml.Vm.Gc.AllocLarge.allocate
#print axioms OCaml.Vm.Gc.AllocLargeWrapper.allocate
#print axioms OCaml.Vm.Gc.BestFitFallback.highBitmapMemory_obstruction
#print axioms OCaml.Vm.Gc.BestFitFallback.no_representation_only_zero_bitmap
