import OCaml.Vm.Boot.Startup.ParameterPresent
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The complete parameter-parser return preserves all runtime/allocator facts. -/
theorem parameter_present_ready {H capacity sp env entry ra s0 s1 s2 s3 s4 s5 s6 byte before after}
    (ready : RuntimeReady H capacity sp ra before)
    (input : ParameterPresentInput sp env entry ra s0 s1 s2 s3 s4 s5 s6 byte before)
    (post : WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
      (parameterPresentLog sp entry ra s0 s1 s2 s3 s4 s5 s6) before ra (parameterValuePointer entry)
      (parameterPresentRegs sp env entry ra s0 s1 s2 s3 s4 s5 s6) after) :
    RuntimeReady H capacity sp ra after := by
  apply ready.stack_log post (by decide) ?_ (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) input.aligned input.frame (parameterPresentLog_inside input.frame)
  simp only [parameterPresentRegs, parameterValueReturnRegs, parameterPresentKept,
    List.cons_append, List.nil_append, keysG]
  decide
end OCaml.Vm.Boot.Startup
