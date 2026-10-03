import OCaml.Vm.Gc.ForwardedAccess
import OCaml.Vm.Gc.OldifyReturn

namespace OCaml.Vm.Gc.Forwarded
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

theorem Post.saved_same {source root sp before after}
    (post : Post source root before after)
    (outside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange [(root.toNat, 8, word before source.toNat)]
        (sp + BitVec.ofNat 64 off).toNat 8) : OldifyReturn.SavedSame sp before after := by
  intro off member
  rw [post.memory]
  exact bytesT_writeLog_out _ (outside off member)

theorem Post.return_input {source root sp before after}
    (post : Post source root before after)
    (stack : gprGet before.σ 2 = some sp)
    (windows : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8)
    (same : OldifyReturn.SavedSame sp before after)
    (aligned : (OldifyReturn.returnWord sp before).toNat % 4 = 0) :
    OldifyReturn.Input sp after := by
  have keep : gprGet after.σ 2 = gprGet before.σ 2 := by
    apply post.machine.frame Register.x2 (by decide)
    intro n hn
    have h := written n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  refine ⟨post.machine.good, post.machine.minstret, post.machine.tick, post.code,
    ⟨keep.trans stack, True.intro⟩, windows, ?_⟩
  rw [same.returnWord]
  exact aligned

/-- Header-to-return path, including the native epilogue. Saved words are
those in the entry memory; the prologue must establish their caller values. -/
structure Returned (source root sp : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  minstret : ∃ v, after.σ.regs.get? Register.minstret = some v
  tick : after.tick < 2
  code : Code.Caml_oldify_oneLoaded after.σ.mem
  memory : after.σ.mem = writeLog before.σ.mem [(root.toNat, 8, word before source.toNat)]
  rootWord : word after root.toNat = word before source.toNat
  pc : PCAt (OldifyReturn.returnWord sp before) after
  registers : GHolds after.σ (OldifyReturn.restored sp before)
  output : after.σ.sailOutput = before.σ.sailOutput
  native : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
    (∀ n ∈ wrChain blocks ++ wrChain OldifyReturn.blocks, (gprReg n == r) = false) →
    after.σ.regs.get? r = before.σ.regs.get? r

theorem forwarded_return {source root sp c} (input : Input source root c)
    (stack : gprGet c.σ 2 = some sp)
    (windows : ∀ off ∈ OldifyReturn.offsets, ReadWindow (sp + BitVec.ofNat 64 off) 8)
    (outside : ∀ off ∈ OldifyReturn.offsets,
      OutLRange [(root.toNat, 8, word c source.toNat)] (sp + BitVec.ofNat 64 off).toNat 8)
    (aligned : (OldifyReturn.returnWord sp c).toNat % 4 = 0) :
    FnSummary pc (fun d => d = c) (Returned source root sp c) := by
  constructor
  apply Vsa.Logic.Triple.seq (forwarded_machine input).run
  intro middle copied
  have same := copied.saved_same outside
  obtain ⟨after, run, returned⟩ :=
    (OldifyReturn.return_machine (copied.return_input stack windows same aligned)).run
      middle ⟨copied.pc, rfl⟩
  refine ⟨after, run, ⟨returned.machine.good, returned.machine.minstret, returned.machine.tick,
    returned.code, returned.memory.trans copied.memory, ?_, ?_, ?_,
    returned.machine.output.trans copied.machine.output, ?_⟩⟩
  · simpa only [word, returned.memory] using copied.rootWord
  · simpa only [same.returnWord] using returned.pc
  · simpa only [same.restored] using returned.registers
  · intro r noise untouched
    exact (returned.machine.frame r noise (fun n hn => untouched n (List.mem_append_right _ hn))).trans
      (copied.machine.frame r noise (fun n hn => untouched n (List.mem_append_left _ hn)))

end OCaml.Vm.Gc.Forwarded
