import OCaml.Vm.Gc.MopupForwarded
import OCaml.Vm.Gc.OldifyResume

namespace OCaml.Vm.Gc.MopupCall

/-- Generated post-return jump to the suffix header/counter advance. -/
def resume : OldifyBridge.Resume site :=
  ⟨resumeBlocks, resumePc, advancePc, call_link, resume_code, resume_ok,
    resume_access, resume_log, resume_regs, resume_exit, resume_written⟩

abbrev ResumedPost := OldifyBridge.ResumedPost site resume
abbrev resume_forwarded := @OldifyBridge.resume_forwarded site resume
abbrev forwarded_resume := @OldifyBridge.forwarded_resume site resume

end OCaml.Vm.Gc.MopupCall
