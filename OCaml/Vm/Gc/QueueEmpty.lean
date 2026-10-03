import OCaml.Vm.Gc.QueueResume

namespace OCaml.Vm.Gc.WorkQueue
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable MopupPop

/-- Platform and runtime global pin at either queue test. -/
structure EmptyInput (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_mopupLoaded c.σ.mem
  registers : GHolds c.σ regs
  empty : word c Layout.sym_oldify_todo_list = 0

def emptyLoads (c : Config) := [read8 c.σ.mem Layout.sym_oldify_todo_list]

/-- Total readback of the represented empty head selects the exit branch. -/
theorem empty_access (resume : Bool) {c} (input : EmptyInput c) :
    ChainAccess c.σ.mem regs (emptyLoads c) (emptyBlocks resume) := by
  cases resume <;> apply ChainAccess.cons ?_ ChainAccess.nil
  all_goals constructor
  all_goals first
    | (simp only [emptyBlocks, Bool.false_eq_true, ite_false, ite_true,
        caml_oldify_mopupX9d88FSeg, caml_oldify_mopupX9d00TSeg, AccessPlan]
       chain_facts True.intro
       apply todo_window.read.ld rfl ?_ (read8_pins _ _)
       simp [eaddrM, mkLine, decodeM, regs, srcVal, lookupG,
         Functions.sign_extend, Sail.BitVec.signExtend])
    | (simpa [TermFactsO, TermFactsT, runGM, stepGM, wvalM, srcVal, lookupG, eraseG,
        mkLine, decodeM, regs, emptyLoads, read8_value, word, guardB] using input.empty)

/-- Queue exhaustion reaches ephemeron processing with memory/output unchanged.
The ephemeron phase and eventual native return remain separate obligations. -/
structure EmptyPost (resume : Bool) (before after : Config) : Prop where
  machine : BlockPost (emptyBlocks resume) (emptyPc resume) regs (emptyLoads before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt emptyExit after
  code : Code.Caml_oldify_mopupLoaded after.σ.mem

theorem empty_machine (resume : Bool) {c} (input : EmptyInput c) :
    FnSummary (emptyPc resume) (fun d => d = c) (EmptyPost resume c) := by
  have summary := block_summary (emptyBlocks resume) (emptyPc resume) regs (emptyLoads c) c
    ⟨input.good, input.minstret, input.registers, by decide,
      chainPlan_facts (empty_code resume input.code) (empty_access resume input),
      empty_ok resume, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, empty_log]; rfl
  refine ⟨post, memory, ?_, memory ▸ input.code⟩
  rw [PCAt, post.pc, empty_pc]

/-- The last completed block supplies the concrete empty-exit input. -/
theorem PopScanPost.empty_input {q fields pl cp tag before after}
    (input : PopInput q [] pl before)
    (post : PopScanPost q [] fields pl cp tag before after) : EmptyInput after := by
  refine ⟨post.good, post.minstret, post.tick, post.code, ?_, ?_⟩
  · have keep : gprGet after.σ 23 = gprGet before.σ 23 :=
      post.native Register.x23 (by decide) (by decide)
    exact ⟨keep.trans (gholds_lookup _ input.registers rfl), True.intro⟩
  · exact post.queue.root

end OCaml.Vm.Gc.WorkQueue
