import OCaml.Vm.Boot.Startup.FindFound
import OCaml.Vm.Boot.Startup.FindTail
namespace OCaml.Vm.Boot.Startup
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The delimiter save is below the saved-register bank, while getenv's output
slot is above the callee frame. Both stores preserve the entire bank. -/
theorem findFound_word {sp pointer offset} {before after : Config} (frame : NativeFrame sp 80)
    (high : sp.toNat ≤ offset.toNat)
    (memory : after.σ.mem = writeLog before.σ.mem (findFoundLog sp pointer offset))
    {off : Nat} (lower : 16 ≤ off) (upper : off + 8 ≤ 80) :
    bytesT after.σ.mem (nativeFrameBase sp 80 + off) 8 = bytesT before.σ.mem (nativeFrameBase sp 80 + off) 8 := by
  rw [memory]
  apply bytesT_writeLog_out
  have address : (nativeStack sp 80 + 8#64).toNat = nativeFrameBase sp 80 + 8 := by
    rw [nativeStack, frame.address 8 (by decide), frame.slot_nat (by decide)]
  unfold findFoundLog
  rw [address]
  change (_ ≤ _ ∨ _ ≤ _) ∧ (_ ≤ _ ∨ _ ≤ _) ∧ True
  refine ⟨Or.inr (by dsimp only; omega), Or.inl ?_, trivial⟩
  have enough := frame.lower
  unfold nativeFrameBase
  omega

/-- Read the delimiter back after the disjoint caller-offset store. -/
theorem findFound_pointer {sp pointer offset} {before after : Config} (frame : NativeFrame sp 80)
    (high : sp.toNat ≤ offset.toNat)
    (memory : after.σ.mem = writeLog before.σ.mem (findFoundLog sp pointer offset)) :
    bytesT after.σ.mem (nativeFrameBase sp 80 + 8) 8 = pointer := by
  have address : (nativeStack sp 80 + 8#64).toNat = nativeFrameBase sp 80 + 8 := by
    rw [nativeStack, frame.address 8 (by decide), frame.slot_nat (by decide)]
  rw [memory, findFoundLog, address]
  change bytesT (writeLog (writeLog before.σ.mem [(nativeFrameBase sp 80 + 8, 8, pointer)])
    [(offset.toNat, 4, 0#64)]) (nativeFrameBase sp 80 + 8) 8 = pointer
  rw [bytesT_writeLog_out _ (show OutLRange [(offset.toNat, 4, 0#64)] (nativeFrameBase sp 80 + 8) 8 from ?_)]
  · exact word_writeLog _ _ _
  · refine ⟨Or.inl ?_, trivial⟩
    have enough := frame.lower
    unfold nativeFrameBase
    omega

/-- Carry all search caller registers through its two successful-path stores. -/
theorem FindReturnSaved.found {sp pointer offset ra s1 s2 s3 s5 s6} {before after : Config}
    (saved : FindReturnSaved sp ra s1 s2 s3 s5 s6 before) (frame : NativeFrame sp 80)
    (high : sp.toNat ≤ offset.toNat)
    (memory : after.σ.mem = writeLog before.σ.mem (findFoundLog sp pointer offset)) :
    FindReturnSaved sp ra s1 s2 s3 s5 s6 after := by
  constructor
  · exact (findFound_word frame high memory (by decide) (by decide)).trans saved.caller
  · exact (findFound_word frame high memory (by decide) (by decide)).trans saved.saved1
  · exact (findFound_word frame high memory (by decide) (by decide)).trans saved.saved2
  · exact (findFound_word frame high memory (by decide) (by decide)).trans saved.saved3
  · exact (findFound_word frame high memory (by decide) (by decide)).trans saved.saved5
  · exact (findFound_word frame high memory (by decide) (by decide)).trans saved.saved6
end OCaml.Vm.Boot.Startup
