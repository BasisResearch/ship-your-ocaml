import OCaml.Vm.Primitives.Format.AllocSprintfNative

-- Every theorem introduced by the decimal native composition checkpoint.
#print axioms Vsa.Densify.insert_observed_at
#print axioms Vsa.Densify.applyW_observed_at
#print axioms Vsa.Densify.writeLog_observed_at
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.stored_word
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.ldv_word
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.entry_log
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.entry_inside
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.entry_frame
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.entry_words
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.pro_arguments
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.enter
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.to_return
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.finish_return
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.native_return
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.NativePost.live
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.NativePost.object

-- Compatibility after separating static Requirements from stateful Memory.
#print axioms OCaml.Vm.Primitives.InitializedString.Memory.transport
#print axioms OCaml.Vm.Primitives.InitializedString.Memory.input
#print axioms OCaml.Vm.Primitives.InitializedString.allocate
#print axioms OCaml.Vm.Primitives.InitializedString.initialized_string_nursery
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.short_initialized

-- Decoded call targets and the decimal bound used at the two call splices.
#print axioms OCaml.Vm.Primitives.Format.AllocSprintf.pro_call_target
#print axioms OCaml.Vm.Primitives.Format.AllocSprintf.copy_call_target
#print axioms OCaml.Vm.Primitives.InitializedString.save_call_target
#print axioms OCaml.Vm.Primitives.InitializedString.arguments_call_target
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.decimal_fits
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.decimal_buffer
#print axioms OCaml.Vm.Primitives.Format.AllocSprintfLong.decimal_nursery_small
