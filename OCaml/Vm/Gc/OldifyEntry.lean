import OCaml.Vm.Gc.Generated.OldifyEntry
import OCaml.Vm.Gc.CodeFrame

namespace OCaml.Vm.Gc.OldifyEntry
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Pointer-branch control from the actual argument's parity. -/
theorem head_control (R : Nat → BitVec 64) (even : (R 10).toNat % 2 = 0) :
    TermFactsO (runGM headBlock.body (regs R) []) headBlock.term := by
  rw [head_regs]
  have low : R 10 &&& 1#64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_and] using even
  simp [headBlock, caml_oldify_oneX9a70FSeg, TermFactsO, TermFactsT,
    afterHead, srcVal, lookupG, low, guardB]

theorem access (R : Nat → BitVec 64) (mem : Std.ExtHashMap Nat (BitVec 8))
    (windows : ∀ cell ∈ saves, WriteWindow (frameSp R + BitVec.ofNat 64 cell.2) 8)
    (even : (R 10).toNat % 2 = 0) : ChainAccess mem (regs R) [] blocks := by
  rw [blocks_eq]
  apply ChainAccess.cons ⟨head_access R mem windows, head_control R even⟩
  rw [head_regs]
  change ChainAccess _ (afterHead R) [] [saveBlock]
  exact ChainAccess.cons ⟨save_access R _ windows, True.intro⟩ ChainAccess.nil

/-- Real non-immediate entry: saved native registers and argument pins are
provided by the caller, with writable windows for the decoded stack slots. -/
structure Input (R : Nat → BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  code : Code.Caml_oldify_oneLoaded c.σ.mem
  registers : GHolds c.σ (regs R)
  windows : ∀ cell ∈ saves, WriteWindow (frameSp R + BitVec.ofNat 64 cell.2) 8
  even : (R 10).toNat % 2 = 0

/-- Stops at oldify's nursery-range test. It has installed the native frame
and runtime constants but has not yet read the source header. -/
structure Post (R : Nat → BitVec 64) (before after : Config) : Prop where
  machine : BlockPost blocks pc (regs R) [] before after
  memory : after.σ.mem = writeLog before.σ.mem (saveLog saves R)
  pc : PCAt exitPc after
  registers : GHolds after.σ (afterSave R)
  code : Code.Caml_oldify_oneLoaded after.σ.mem

theorem entry_machine {R c} (input : Input R c) :
    FnSummary pc (fun d => d = c) (Post R c) := by
  have facts := chainPlan_facts (code_facts input.code) (access R c.σ.mem input.windows input.even)
  have summary := block_summary blocks pc (regs R) [] c
    ⟨input.good, input.minstret, input.registers, by change KeysOK entryKeys; decide,
      facts, chain_ok, input.tick⟩
  apply summary.weaken (fun _ h => h)
  intro after post
  refine ⟨post, ?_, ?_, ?_, oldifyCode_after input.code facts post⟩
  · rw [post.memory, effect]
  · rw [PCAt, post.pc, endpoint]
  · simpa only [OldifyEntry.registers] using post.regs

end OCaml.Vm.Gc.OldifyEntry
