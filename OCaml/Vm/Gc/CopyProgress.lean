import OCaml.Vm.Gc.ScanProgress
import OCaml.Vm.Gc.CopyEffect

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- A verbatim-copy effect fits any scan footprint containing its destination
suffix. The expected word may come from a relocation invariant; this route
requires it to equal the source word observed before the real store. -/
theorem CopyEffect.progress {writes a b count start i before after footprint expected}
    (post : CopyEffect writes (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 i) before after)
    (geometry : Geometry a b count) (lower : start ≤ i) (bound : i < count)
    (header : (word before (b - 8)).toNat / 1024 = count)
    (contains : ∀ x, OutW footprint x → OutW (scanWindow b start count) x)
    (value : word before (a + 8 * i) = expected i) :
    ScanProgress writes a b count start i footprint expected before after := by
  have log : copyLog (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a) before =
      [(b + 8 * i, 8, word before (a + 8 * i))] := by
    simp only [copyLog, BitVec.add_comm _ (scanPtr a i), scanPtr_delta,
      geometry.targetRange.ptr_nat (Nat.le_of_lt bound), geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)]
  have memory : after.σ.mem = writeLog before.σ.mem [(b + 8 * i, 8, word before (a + 8 * i))] := by
    rw [post.memory, log]
  have frame : FrameOn (scanWindow b start count) before.σ.mem after.σ.mem := by
    rw [memory]
    apply frameOn_writeLog
    change ((b + 8 * start ≤ b + 8 * i ∧ b + 8 * i + 8 ≤ b + 8 * count) ∨ False) ∧ True
    exact ⟨Or.inl ⟨by omega, by omega⟩, True.intro⟩
  refine ⟨post.good, post.minstret, post.tick, post.code, ?_, ?_,
    (fun x hx => frame x (contains x hx)), ?_, ?_, post.output, post.native⟩
  · have next := post.pc
    rw [again_eq geometry bound header] at next
    simpa only [decide_eq_true_eq] using next
  · simpa only [scanPtr_succ, BitVec.ofNat_add] using post.registers
  · simpa only [BitVec.add_comm _ (scanPtr a i), scanPtr_delta,
      geometry.targetRange.ptr_nat (Nat.le_of_lt bound),
      geometry.sourceRange.ptr_nat (Nat.le_of_lt bound), value] using post.destination
  · intro j _ old
    change bytesT after.σ.mem _ 8 = bytesT before.σ.mem _ 8
    rw [memory]
    apply bytesT_writeLog_out
    exact ⟨Or.inl (by omega), True.intro⟩

end OCaml.Vm.Gc.FieldCopy
