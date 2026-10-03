import OCaml.Vm.Gc.ForwardedField
import OCaml.Vm.Gc.ScanGeometry

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable
open OCaml.Vm.Reloc

/-- The exact native-save/root footprint preserves every separate word. -/
theorem AdvancedPost.word_frame {R before after clobbers a}
    (post : AdvancedPost R before after clobbers)
    (outside : OutLRange (ForwardedCall.effect (linked R) before) a 8) :
    word after a = word before a := by
  change bytesT after.σ.mem a 8 = _
  rw [post.memory, bytesT_writeLog_out _ outside]
  rfl

/-- A separate target header makes the machine's post-call guard equal to
its pre-call guard; no unchanged-memory premise is assumed for the callee. -/
theorem againAfterCall_frame {R c}
    (outside : OutLRange (ForwardedCall.effect (linked R) c) (R 19 - 8#64).toNat 8) :
    againAfterCall R c = FieldCopy.advanceAgain (R 19) (R 9) c := by
  unfold againAfterCall FieldCopy.advanceAgain word
  rw [bytesT_writeLog_out _ outside]

/-- Typed relocation follows from the forwarding word supplied by the
partial relocation invariant. The Eqv transport also moves the slot. -/
theorem AdvancedPost.slot_relocates {R before after clobbers μ pl v sourceSlot}
    (post : AdvancedPost R before after clobbers)
    (represented : (Eqv.val v id).P pl sourceSlot before)
    (sourceWord : word before sourceSlot = R 10)
    (forwarding : word before (R 10).toNat = relocWord μ pl v (R 10)) :
    (Eqv.val v id).P (reloc μ pl) (R 11).toNat after := by
  apply (Eqv.val v id).transport μ pl sourceSlot (R 11).toNat before after represented
  change word after (R 11).toNat = relocWord μ pl v (word before sourceSlot)
  rw [post.destination, sourceWord, forwarding]

/-- Header size and bounded counters identify the real forwarded-call
back edge with the scan's decreasing natural-number bound. -/
theorem againAfterCall_count {R c b count i}
    (range : WordRange b count) (bound : i < count)
    (target : R 19 = BitVec.ofNat 64 b) (index : R 9 = BitVec.ofNat 64 i)
    (outside : OutLRange (ForwardedCall.effect (linked R) c) (R 19 - 8#64).toNat 8)
    (header : (word c (b - 8)).toNat / 1024 = count) :
    againAfterCall R c = decide (i + 1 < count) := by
  rw [againAfterCall_frame outside, FieldCopy.advanceAgain, target, index,
    FieldCopy.header_nat range, header_words _ count header]
  have upper := range.upper
  simp [guardB, LeanRV64DExecutable.Functions.zopz0zI_u, Sail.BitVec.toNatInt,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end OCaml.Vm.Gc.MopupCall
