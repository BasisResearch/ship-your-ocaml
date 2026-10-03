import OCaml.Vm.Gc.ForwardedEffect
import OCaml.Vm.Gc.ScanProgress

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Native saves and the destination store lie in the scan's permitted
footprint, outside its header and previously scanned fields. The enclosing
heap/native-stack geometry supplies these finite-log separation facts. -/
structure ScanFootprint (R : Nat → BitVec 64) (c : Config)
    (footprint : List W) (b start i : Nat) : Prop where
  writes : LogInW footprint (ForwardedCall.effect (linked R) c)
  header : OutLRange (ForwardedCall.effect (linked R) c) (R 19 - 8#64).toNat 8
  previous : ∀ j, start ≤ j → j < i →
    OutLRange (ForwardedCall.effect (linked R) c) (b + 8 * j) 8

/-- Concrete forwarded-field execution supplies the common scan update.
The forwarding value is an observation of the current partial relocation;
the caller need not assume any machine run or unchanged memory. -/
theorem AdvancedPost.progress {R before after writes a b count start i footprint expected}
    (post : AdvancedPost R before after writes)
    (geometry : FieldCopy.Geometry a b count) (bound : i < count)
    (slot : R 8 = scanPtr a i)
    (delta : R 18 = BitVec.ofNat 64 b - BitVec.ofNat 64 a)
    (target : R 19 = BitVec.ofNat 64 b)
    (index : R 9 = BitVec.ofNat 64 i)
    (destination : R 11 = scanPtr b i)
    (separate : ScanFootprint R before footprint b start i)
    (header : (word before (b - 8)).toNat / 1024 = count)
    (forwarding : word before (R 10).toNat = expected i) :
    FieldCopy.ScanProgress writes a b count start i footprint expected before after := by
  refine ⟨post.good, post.minstret, post.tick, post.code, ?_, ?_, ?_, ?_,
    (fun j lower upper => post.word_frame (separate.previous j lower upper)), post.output, post.native⟩
  · have next := post.pc
    rw [againAfterCall_count geometry.targetRange bound target index separate.header header] at next
    simpa only [decide_eq_true_eq] using next
  · simpa only [slot, delta, target, index, scanPtr_succ, BitVec.ofNat_add] using post.registers
  · rw [post.memory]
    exact frameOn_writeLog _ _ _ separate.writes
  · have stored := post.destination.trans forwarding
    simpa only [destination, geometry.targetRange.ptr_nat (Nat.le_of_lt bound)] using stored

end OCaml.Vm.Gc.MopupCall
