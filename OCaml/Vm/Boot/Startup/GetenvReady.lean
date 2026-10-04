import OCaml.Vm.Boot.Startup.Getenv
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Getenv's nested stack effects preserve the complete runtime/allocator state. -/
theorem getenv_ready {H capacity sp name env ra s1 s2 s3 s4 s5 s6 cs before after}
    (ready : RuntimeReady H capacity sp ra before)
    (input : GetenvInput sp name env ra s1 s2 s3 s4 s5 s6 cs before)
    (post : WriteRegistersPost [1, 2, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
      (getenvFullLog sp ra s1 s2 s3 s4 s5 s6) before ra 0#64
      (getenvRegs sp ra s1 s2 s3 s4 s5 s6 name cs.length) after) :
    RuntimeReady H capacity sp ra after := by
  apply ready.stack_log post (by decide) ?_ (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) input.aligned input.frame (getenvFullLog_inside input.frame)
  simp only [getenvRegs, getenvReturnRegs, getenvKeptRegs, getenvSavedRegs,
    List.cons_append, List.nil_append, keysG]
  decide
end OCaml.Vm.Boot.Startup
