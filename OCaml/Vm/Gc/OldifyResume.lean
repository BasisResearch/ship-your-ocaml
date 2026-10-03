import OCaml.Vm.Gc.OldifyBridge

namespace OCaml.Vm.Gc.OldifyBridge
open Vsa.Machine Vsa.Sim Primitives

/-- Generated certificates for a read-only return continuation. Both mopup
oldify sites resume through a jump; their callee and continuation folds share
one proof over these reflected block facts. -/
structure Resume (site : Site) where
  blocks : List BBlock
  entry : BitVec 64
  exit : BitVec 64
  link : site.call.link = entry
  code : ∀ {mem}, Code.Caml_oldify_mopupLoaded mem → ChainCode mem blocks
  shape : ∀ keys, ChainOK entry keys blocks
  access : ∀ mem L, ChainAccess mem L [] blocks
  log : ∀ L lds, (evalBlocks blocks (SegEvalState.init L lds)).log = []
  registers : ∀ L lds, (evalBlocks blocks (SegEvalState.init L lds)).regs = L
  pc : ∀ L lds, evalBlocksPC entry (SegEvalState.init L lds) blocks = exit
  written : wrChain blocks = []

variable (site : Site) (resume : Resume site)

/-- Forwarded-call effects after the concrete mopup return continuation. -/
structure ResumedPost (R : Nat → BitVec 64) (before after : Config) : Prop where
  body : ForwardedCall.Post (linked site R) before after resume.exit
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem resume_forwarded {R before c} (input : ForwardedPost site R before c) :
    FnSummary resume.entry (fun d => d = c) (ResumedPost site resume R before) := by
  let L := OldifyEntry.callerRegs (linked site R)
  have summary := block_summary resume.blocks resume.entry L [] c
    ⟨input.body.good, input.body.minstret, input.body.registers,
      by change KeysOK [2,9,25,24,23,22,21,20,19,18,8,1]; decide,
      chainPlan_facts (resume.code input.code) (resume.access _ _), resume.shape _, input.body.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, resume.log]; rfl
  refine ⟨⟨post.good, post.minstret, post.tick, memory ▸ input.body.code,
    memory.trans input.body.memory, ?_, ?_, ?_, post.output.trans input.body.output, ?_⟩,
    memory ▸ input.code⟩
  · simpa only [word, memory] using input.body.root
  · rw [PCAt, post.pc, resume.pc]
  · simpa only [resume.registers] using post.regs
  · intro r noise untouched
    exact (post.frame r noise (by simp only [resume.written, List.not_mem_nil, false_implies, implies_true])).trans
      (input.body.native r noise untouched)

theorem forwarded_resume {R domain c} (input : ForwardedCall.Input R domain c)
    (code : Code.Caml_oldify_mopupLoaded c.σ.mem) :
    FnSummary site.call.pc (fun d => d = c) (ResumedPost site resume R c) := by
  constructor
  apply Vsa.Logic.Triple.seq (forwarded site input code).run
  intro returned post
  have pc : PCAt resume.entry returned := by
    simpa only [linked, ite_true, resume.link] using post.body.pc
  exact (resume_forwarded site resume post).run returned ⟨pc,rfl⟩

end OCaml.Vm.Gc.OldifyBridge
