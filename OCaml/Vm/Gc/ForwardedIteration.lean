import OCaml.Vm.Gc.ScanFootprint

namespace OCaml.Vm.Gc.ForwardedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A loaded already-forwarded field executes and advances the shared scan
invariant. The enclosing relocation invariant supplies the observed target;
all machine steps and log separation are discharged by concrete summaries. -/
theorem scan_iteration {R domain a b count start initial i c expected}
    (input : Input R domain c)
    (geometry : FieldCopy.Geometry a b count)
    (slot : R 8 = scanPtr a i)
    (delta : R 18 = BitVec.ofNat 64 b - BitVec.ofNat 64 a)
    (target : R 19 = BitVec.ofNat 64 b)
    (index : R 9 = BitVec.ofNat 64 i)
    (stack : (MopupCall.nativeWindow R).hi ≤ b - 8 ∨
      b + 8 * count ≤ (MopupCall.nativeWindow R).lo)
    (header : (word c (b - 8)).toNat / 1024 = count)
    (forwarding : word c (word c (R 8).toNat).toNat = expected i)
    (scan : FieldCopy.ScanAtWith [1,8,9,10,11,12,14,15] a b count start initial i c
      (MopupCall.scanFootprint R b start count) expected)
    (bound : i < count) :
    ∃ d, Steps c d ∧ FieldCopy.ScanAtWith [1,8,9,10,11,12,14,15] a b count start initial (i + 1) d
      (MopupCall.scanFootprint R b start count) expected := by
  have destination : args R c 11 = scanPtr b i := by
    simp only [args, show ¬ (11 : Nat) = 10 from by decide, ite_false, ite_true, slot, delta]
    rw [BitVec.add_comm, scanPtr_delta]
  have stackBound : (OldifyEntry.frameSp (MopupCall.linked (args R c))).toNat +
      OldifyEntry.maxSlot.2 + 8 ≤ 0x100000000 :=
    stack_bound (OldifyEntry.frameSp R) OldifyEntry.maxSlot.2 (by decide)
      (input.stackWindows OldifyEntry.maxSlot OldifyEntry.max_mem)
  have footprint := MopupCall.scanFootprint_of_geometry (R := args R c) (c := c)
    geometry scan.lower bound stackBound target
    (by rw [destination, geometry.targetRange.ptr_nat (Nat.le_of_lt bound)]) stack
  obtain ⟨d, run, post⟩ := (forwarded_field input).run c ⟨by simpa [bound] using scan.pc, rfl⟩
  have progress := post.progress geometry bound slot delta target index destination footprint header forwarding
  exact ⟨d, run, scan.advance_progress bound progress⟩

end OCaml.Vm.Gc.ForwardedField
