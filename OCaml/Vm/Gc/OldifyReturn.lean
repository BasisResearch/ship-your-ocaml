import OCaml.Vm.Gc.Generated.OldifyReturn
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.OldifyReturn
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Concrete native frame at the common oldify epilogue. Saved values are
read from memory; the caller's stack invariant supplies their identities. -/
structure Input (sp : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs sp)
  windows : ∀ off ∈ offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8
  aligned : (returnWord sp c).toNat % 4 = 0

structure Post (sp : BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs sp) (loads sp before) before after
  memory : after.σ.mem = before.σ.mem
  pc : PCAt (returnWord sp before) after
  registers : GHolds after.σ (restored sp before)
  code : Code.Caml_oldify_oneLoaded after.σ.mem

theorem return_machine {sp c} (input : Input sp c) :
    FnSummary pc (fun d => d = c) (Post sp c) := by
  have access : ChainAccess c.σ.mem (regs sp) (loads sp c) blocks :=
    ChainAccess.cons ⟨restore_access sp c input.windows, control sp c input.aligned⟩ ChainAccess.nil
  have facts := chainPlan_facts (code_facts input.code) access
  have summary := block_summary blocks pc (regs sp) (loads sp c) c
    ⟨input.good, input.minstret, input.registers, by change KeysOK [2]; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  have memory : after.σ.mem = c.σ.mem := by rw [post.memory, no_stores]; rfl
  refine ⟨post, memory, ?_, ?_, memory ▸ input.code⟩
  · rw [PCAt, post.pc, endpoint sp c input.aligned]
  · have holds := post.regs
    change GHolds after.σ (runGM block.body (regs sp) (loads sp c)) at holds
    rwa [restored_regs] at holds

/-- Equality of the saved words consumed by the generated epilogue. Heap
writes preserve these observations when separated from the native frame. -/
def SavedSame (sp : BitVec 64) (before after : Config) : Prop :=
  ∀ off ∈ offsets, bytesT after.σ.mem (sp + BitVec.ofNat 64 off).toNat 8 =
    bytesT before.σ.mem (sp + BitVec.ofNat 64 off).toNat 8

theorem SavedSame.returnWord {sp before after} (same : SavedSame sp before after) :
    returnWord sp after = returnWord sp before := same _ (by decide)

theorem SavedSame.restored {sp before after} (same : SavedSame sp before after) :
    restored sp after = restored sp before := by
  unfold OldifyReturn.restored
  congr 1
  apply List.map_congr_left
  intro cell member
  simp only [List.mem_reverse] at member
  exact congrArg (fun w => (cell.1, w)) (same cell.2 (slot_offset cell member))

end OCaml.Vm.Gc.OldifyReturn
