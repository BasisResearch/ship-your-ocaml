import OCaml.Vm.Boot.Startup.ParameterQuery
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Each generated parameter-query call returns with complete runtime readiness. -/
theorem parameter_query_ready {fallback H capacity sp env ra s0 s1 s2 s3 s4 s5 s6 before after}
    (ready : RuntimeReady H capacity sp ra before)
    (input : ParameterQueryInput fallback sp env ra s0 s1 s2 s3 s4 s5 s6 before)
    (post : WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
      (secureEnvLog sp (parameterCall fallback).link s0 s1 s2 s3 s4 s5 s6) before (parameterCall fallback).link 0#64
      (secureEnvRegs sp (parameterCall fallback).link s0 s1 s2 s3 s4 s5 s6
        (parameterName fallback) (parameterChars fallback).length) after) :
    RuntimeReady H capacity sp (parameterCall fallback).link after := by
  apply ready.stack_log post (by decide) ?_ (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) (by cases fallback <;> decide) input.frame (secureEnvLog_inside input.frame)
  simp only [secureEnvRegs, getenvRegs, getenvReturnRegs, getenvKeptRegs, getenvSavedRegs,
    List.cons_append, List.nil_append, keysG]
  decide
end OCaml.Vm.Boot.Startup
