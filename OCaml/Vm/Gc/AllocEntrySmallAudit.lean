import OCaml.Vm.Gc.AllocEntrySmall
import OCaml.Vm.Gc.AllocEntryLarge
import OCaml.Vm.Gc.AllocWrapper

/-! Focused original-small audit. Full OCaml.Audit remains the lead gate. -/

#print axioms OCaml.Vm.Gc.logInW_member
#print axioms OCaml.Vm.Gc.AllocOriginal.native_bounds
#print axioms OCaml.Vm.Gc.AllocOriginal.prologue_inside
#print axioms OCaml.Vm.Gc.AllocOriginal.prologue_read
#print axioms OCaml.Vm.Gc.AllocOriginal.prepared_representation
#print axioms OCaml.Vm.Gc.AllocOriginal.initialized_read
#print axioms OCaml.Vm.Gc.AllocOriginal.ready_read
#print axioms OCaml.Vm.Gc.AllocOriginal.saved
#print axioms OCaml.Vm.Gc.AllocOriginal.color
#print axioms OCaml.Vm.Gc.AllocOriginal.continuation
#print axioms OCaml.Vm.Gc.AllocOriginal.finish_memory
#print axioms OCaml.Vm.Gc.AllocOriginal.finish_read
#print axioms OCaml.Vm.Gc.AllocOriginal.live
#print axioms OCaml.Vm.Gc.AllocOriginal.finished_representation
#print axioms OCaml.Vm.Gc.AllocOriginal.logWindows
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.native_bounds
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.prepared_representation
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.entry_input
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.static_out
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.source_header
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.selection
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.prefix_inside
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Selection.header_inside
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.free_outside
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.continuation
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.callee
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Post.path_spec
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.effect_inside
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Input.returned
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Returned.selected_spec
#print axioms OCaml.Vm.Gc.AllocEntrySmall.allocate
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Post.logWindows
#print axioms OCaml.Vm.Gc.AllocEntrySmall.Post.live
#print axioms OCaml.Vm.Gc.BestFitFallback.small_prefix_inside
#print axioms OCaml.Vm.Gc.BestFitFallback.small_remnant_inside
#print axioms OCaml.Vm.Gc.BestFitFallback.small_route_inside
#print axioms OCaml.Vm.Gc.BestFitFallback.EntrySmallReturned.class_bounds
#print axioms OCaml.Vm.Gc.BestFitFallback.EntryNextReturned.split_size
#print axioms OCaml.Vm.Gc.BestFitFallback.EntrySmallReturned.log_inside
#print axioms OCaml.Vm.Gc.BestFitFallback.EntrySmallReturned.result_interval
#print axioms OCaml.Vm.Gc.BestFitFallback.EntrySmallReturned.counter_nat
#print axioms OCaml.Vm.Gc.BestFitFallback.EntrySmallReturned.frame
#print axioms OCaml.Vm.Gc.BestFitFallback.smallRefund_of_memory

#print axioms OCaml.Vm.Gc.AllocFinish.CalleePost.finish
#print axioms OCaml.Vm.Gc.AllocFinish.Post.header
#print axioms OCaml.Vm.Gc.AllocWrapperCore.Entered.complete
#print axioms OCaml.Vm.Gc.AllocWrapperCore.header_of_effect
#print axioms OCaml.Vm.Gc.AllocExact.allocate
#print axioms OCaml.Vm.Gc.AllocWrapper.allocate
#print axioms OCaml.Vm.Gc.AllocEntryLarge.allocate
#print axioms OCaml.Vm.Gc.BestFitFallback.allocate_entry_small
#print axioms OCaml.Vm.Gc.BestFitFallback.highBitmapMemory_obstruction
#print axioms OCaml.Vm.Gc.BestFitFallback.no_representation_only_zero_bitmap
