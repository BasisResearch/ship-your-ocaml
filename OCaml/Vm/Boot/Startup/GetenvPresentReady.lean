import OCaml.Vm.Boot.Startup.GetenvPresent
import OCaml.Vm.Boot.Startup.RuntimeStack
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A successful getenv call preserves the complete running runtime contract. -/
theorem getenv_present_ready {H capacity sp env entry name ra s0 s1 s2 s3 s4 s5 s6 count before after}
    (ready : RuntimeReady H capacity sp ra before) (frame : NativeFrame sp 112)
    (post : WriteRegistersPost [1, 2, 8, 9, 10, 11, 12, 14, 15, 18, 19, 20, 21, 22]
      (getenvPresentLog sp ra s0 s1 s2 s3 s4 s5 s6 (nameCursor entry count)) before ra (nameCursor entry count + 1#64)
      (getenvPresentRegs sp ra s0 s1 s2 s3 s4 s5 s6 env entry name count) after) :
    RuntimeReady H capacity sp ra after := by
  apply ready.stack_log post (by decide) ?_ (by decide)
    (gholds_lookup (n := 2) _ post.regs (by rfl))
    (gholds_lookup (n := 1) _ post.regs (by rfl)) ready.aligned frame (getenvPresentLog_inside frame)
  simp only [getenvPresentRegs, getenvReturnRegs, getenvPresentKeptRegs, getenvSavedRegs,
    List.cons_append, List.nil_append, keysG]
  decide
end OCaml.Vm.Boot.Startup
