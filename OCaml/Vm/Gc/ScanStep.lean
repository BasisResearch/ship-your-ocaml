import OCaml.Vm.Gc.ScanState
import OCaml.Vm.Gc.CopyEffect

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- One shared invariant update for either concrete verbatim-copy route.
The write-set parameter preserves each route's precise native frame. -/
theorem ScanAtWith.advance {writes a b count start initial i c d}
    (h : ScanAtWith writes a b count start initial i c)
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (bound : i < count)
    (post : CopyEffect writes (scanPtr a i) (BitVec.ofNat 64 b - BitVec.ofNat 64 a)
      (BitVec.ofNat 64 b) (BitVec.ofNat 64 i) c d) :
    ScanAtWith writes a b count start initial (i + 1) d := by
  let slot := scanPtr a i
  let delta := BitVec.ofNat 64 b - BitVec.ofNat 64 a
  let target := BitVec.ofNat 64 b
  let index := BitVec.ofNat 64 i
  have source : word c (a + 8 * i) = word initial (a + 8 * i) := by
    apply word_frame h.memory
    have separate := geometry.separate
    omega
  have sameHeader : word c (b - 8) = word initial (b - 8) := by
    apply word_frame h.memory
    exact Or.inl (by have lower := geometry.targetRange.lower; omega)
  have log : copyLog slot delta c = [(b + 8 * i, 8, word c (a + 8 * i))] := by
    simp only [copyLog, slot, delta, BitVec.add_comm _ (scanPtr a i), scanPtr_delta,
      geometry.targetRange.ptr_nat (Nat.le_of_lt bound), geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)]
  have memory : d.σ.mem = writeLog c.σ.mem [(b + 8 * i, 8, word c (a + 8 * i))] := by
    rw [post.memory, log]
  have frame : FrameOn (scanWindow b start count) c.σ.mem d.σ.mem := by
    rw [memory]
    apply frameOn_writeLog
    change ((b + 8 * start ≤ b + 8 * i ∧ b + 8 * i + 8 ≤ b + 8 * count) ∨ False) ∧ True
    exact ⟨Or.inl ⟨by have := h.lower; omega, by omega⟩, True.intro⟩
  refine ⟨post.good, post.minstret, post.tick,
    post.code, by have := h.lower; omega, by omega, ?_, ?_,
    (fun a ha => (frame a ha).trans (h.memory a ha)), ?_,
    post.output.trans h.output, ?_⟩
  · have next := post.pc
    rw [again_eq geometry bound (sameHeader ▸ header)] at next
    simpa only [decide_eq_true_eq] using next
  · simpa only [slot, delta, target, index, scanPtr_succ, BitVec.ofNat_add] using post.registers
  · intro j lower lt
    by_cases current : j = i
    · subst j
      have copied := post.destination
      simpa only [slot, delta, BitVec.add_comm _ (scanPtr a i), scanPtr_delta,
        geometry.targetRange.ptr_nat (Nat.le_of_lt bound),
        geometry.sourceRange.ptr_nat (Nat.le_of_lt bound), source] using copied
    · have old : j < i := by omega
      have unchanged : word d (b + 8 * j) = word c (b + 8 * j) := by
        change bytesT d.σ.mem _ 8 = bytesT c.σ.mem _ 8
        rw [memory]
        apply bytesT_writeLog_out
        exact ⟨Or.inl (by omega), True.intro⟩
      exact unchanged.trans (h.copied j lower old)
  · intro r noise notWritten
    exact (post.native r noise notWritten).trans
      (h.native r noise notWritten)

end OCaml.Vm.Gc.FieldCopy
