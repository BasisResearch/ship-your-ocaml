import OCaml.Vm.Gc.Generated.FirstCall
import OCaml.Vm.Gc.OldifyResume

namespace OCaml.Vm.Gc.FirstCall
open Vsa.Machine Vsa.Sim Primitives

/-- The generated first-field JAL instantiates the same callee bridge used
by suffix fields. Its argument setup and return jump are separate spans. -/
def site : OldifyBridge.Site :=
  ⟨call, call_shape, call_decode, call_target, by decide, call_pins⟩

abbrev linked := OldifyBridge.linked site
abbrev ForwardedPost := OldifyBridge.ForwardedPost site

/-- Actual first-field JAL and complete already-forwarded oldify invocation,
returning to the generated first-field link with native registers restored. -/
theorem forwarded {R domain c} (input : ForwardedCall.Input R domain c)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) :
    FnSummary call.pc (fun d => d = c) (ForwardedPost R c) :=
  OldifyBridge.forwarded site input code

/-- The first-field return jump reaches the suffix setup block. -/
def resume : OldifyBridge.Resume site :=
  ⟨resumeBlocks, resumePc, setupPc, call_link, resume_code, resume_ok,
    resume_access, resume_log, resume_regs, resume_exit, resume_written⟩

abbrev ResumedPost := OldifyBridge.ResumedPost site resume

/-- Complete first-field call, forwarded oldify body and actual return jump. -/
theorem forwarded_resume {R domain c} (input : ForwardedCall.Input R domain c)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) :
    FnSummary call.pc (fun d => d = c) (ResumedPost R c) :=
  OldifyBridge.forwarded_resume site resume input code

end OCaml.Vm.Gc.FirstCall
