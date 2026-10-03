import OCaml.Vm.Gc.MopupForwarded

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives

/-- Same forwarded-call effects after mopup's real return jump. The PC is
now the header-controlled counter advance, not the caller link instruction. -/
structure ResumedPost (R : Nat → BitVec 64) (before after : Config) : Prop where
  body : ForwardedCall.Post (linked R) before after advancePc
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem resume_forwarded {R before c} (input : ForwardedPost R before c) :
    FnSummary resumePc (fun d => d = c) (ResumedPost R before) := by
  let L := OldifyEntry.callerRegs (linked R)
  have access : ChainAccess c.σ.mem L [] resumeBlocks :=
    ChainAccess.cons ⟨True.intro, True.intro⟩ ChainAccess.nil
  have summary := block_summary resumeBlocks resumePc L [] c
    ⟨input.body.good, input.body.minstret, input.body.registers,
      by change KeysOK [2,9,25,24,23,22,21,20,19,18,8,1]; decide,
      chainPlan_facts (resume_code input.code) access, resume_ok _, input.body.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, resume_log]; rfl
  refine ⟨⟨post.good, post.minstret, post.tick, memory ▸ input.body.code,
    memory.trans input.body.memory, ?_, ?_, ?_, post.output.trans input.body.output, ?_⟩,
    memory ▸ input.code⟩
  · simpa only [word, memory] using input.body.root
  · rw [PCAt, post.pc, resume_exit]
  · simpa only [resume_regs] using post.regs
  · intro r noise untouched
    exact (post.frame r noise (by simp only [resume_written, List.not_mem_nil, false_implies, implies_true])).trans
      (input.body.native r noise untouched)

/-- Mopup's young-field JAL, complete already-forwarded oldify callee, and
actual return jump, composed at their generated PCs. -/
theorem forwarded_resume {R domain c} (input : ForwardedCall.Input R domain c)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) :
    FnSummary call.pc (fun d => d = c) (ResumedPost R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (forwarded input code).run
  intro returned post
  have pc : PCAt resumePc returned := by
    simpa only [linked, ite_true, call_link] using post.body.pc
  exact (resume_forwarded post).run returned ⟨pc,rfl⟩

end OCaml.Vm.Gc.MopupCall
