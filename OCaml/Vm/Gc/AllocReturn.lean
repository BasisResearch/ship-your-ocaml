import OCaml.Vm.Gc.Generated.AllocReturn
import OCaml.Vm.Gc.CodeFrame
import OCaml.Vm.Primitives.MemoryFrame

namespace OCaml.Vm.Gc.AllocReturn
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Concrete native frame at the successful minor-allocation epilogue. Saved values are
read from memory; the caller's stack invariant supplies their identities. -/
structure Input (sp hp : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_alloc_shr_for_minor_gcLoaded c.σ.mem
  registers : GHolds c.σ (regs sp hp)
  windows : ∀ off ∈ offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8
  aligned : (returnWord sp hp c).toNat % 4 = 0

structure Post (sp hp : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs sp hp) (loads sp hp before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (returnWord sp hp before) after
  registers : GHolds after.σ (restored sp hp before)
  code : Code.Caml_alloc_shr_for_minor_gcLoaded after.σ.mem

theorem return_machine {sp hp c} (input : Input sp hp c) :
    FnSummary pc (fun d => d = c) (Post sp hp c) := by
  have access : ChainAccess c.σ.mem (regs sp hp) (loads sp hp c) blocks :=
    ChainAccess.cons ⟨restore_access sp hp c input.windows, control sp hp c input.aligned⟩ ChainAccess.nil
  have facts := chainPlan_facts (code_facts input.code) access
  have summary := block_summary blocks pc (regs sp hp) (loads sp hp c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2,10]; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, no_stores]; rfl
  refine ⟨post, memory, ?_, ?_, memory ▸ input.code⟩
  · rw [PCAt, post.pc, endpoint sp hp c input.aligned]
  · have holds := post.regs
    change GHolds after.σ (runGM block.body (regs sp hp) (loads sp hp c)) at holds
    rwa [restored_regs] at holds

end OCaml.Vm.Gc.AllocReturn
