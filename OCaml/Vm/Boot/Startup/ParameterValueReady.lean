import OCaml.Vm.Boot.Startup.ParameterValueDone
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The present-empty-value return retains the complete running runtime state. -/
theorem parameter_value_ready {H capacity sp ra oldra s0 s1 s2 s3 value before after}
    (ready : RuntimeReady H capacity (nativeStack sp 64) oldra before)
    (frame : NativeFrame sp 64) (aligned : ra.toNat % 4 = 0)
    (post : WriteRegistersPost [8, 19, 18, 9, 15, 1, 2] (parameterValueLog sp s1 s2 s3) before ra value
      (parameterValueReturnRegs sp ra s0 s1 s2 s3 value ++ [(15, 0#64)]) after) :
    RuntimeReady H capacity sp ra after := by
  apply ready.stack_log post (by decide) ?_ (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) aligned frame (parameterValueLog_inside frame)
  simp only [parameterValueReturnRegs, List.cons_append, List.nil_append, keysG]
  decide
end OCaml.Vm.Boot.Startup
