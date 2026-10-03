import OCaml.Vm.Gc.ScanStep
import Vsa.Sim.DeriveLoop

namespace OCaml.Vm.Gc.FieldCopy
open Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- One concrete immediate-field iteration preserves the scan invariant. -/
theorem scan_iteration {a b count start initial i c}
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (immediates : ∀ j, start ≤ j → j < count →
      guardB .BNE (word initial (a + 8 * j) &&& 1#64) 0 = true)
    (h : ScanAt a b count start initial i c) (bound : i < count) :
    ∃ d, Steps c d ∧ ScanAt a b count start initial (i + 1) d := by
  let slot := scanPtr a i
  let delta := BitVec.ofNat 64 b - BitVec.ofNat 64 a
  let target := BitVec.ofNat 64 b
  let index := BitVec.ofNat 64 i
  have source : word c (a + 8 * i) = word initial (a + 8 * i) := by
    apply word_frame h.memory
    have separate := geometry.separate
    omega
  have input : Input slot delta target index c :=
    ⟨h.good, h.minstret, h.registers, h.tick, h.code, geometry.windows bound, by
      change guardB .BNE (word c (scanPtr a i).toNat &&& 1#64) 0 = true
      rw [geometry.sourceRange.ptr_nat (Nat.le_of_lt bound), source]
      exact immediates i h.lower bound⟩
  obtain ⟨d, run, post⟩ := (copy_machine input).run c ⟨by simpa [bound] using h.pc, rfl⟩
  exact ⟨d, run, h.advance geometry header bound (post.effect input)⟩

/-- Shared loop fold, instantiated below by concrete copy summaries. -/
theorem ScanAtWith.loop {writes a b count start initial footprint expected}
    (geometry : Geometry a b count)
    (step : ∀ i, Triple (fun c => ScanAtWith writes a b count start initial i c footprint expected ∧ i < count)
      (ScanAtWith writes a b count start initial (i + 1) · footprint expected)) :
    Triple (fun c => ScanAtWith writes a b count start initial start c footprint expected)
      (fun c => ScanAtWith writes a b count start initial count c footprint expected) := by
  let I := fun c => ScanAtWith writes a b count start initial (scanIndex c) c footprint expected
  let B := fun c => scanIndex c < count
  have body : ∀ n, Triple (fun c => I c ∧ B c ∧ count - scanIndex c = n)
      (fun c => I c ∧ count - scanIndex c < n) := by
    intro n c ⟨h, lt, rank⟩
    obtain ⟨d, run, post⟩ := step (scanIndex c) c ⟨h, lt⟩
    have index := post.index_eq geometry
    refine ⟨d, run, ?_, ?_⟩
    · change ScanAtWith writes a b count start initial (scanIndex d) d footprint expected
      rw [index]; exact post
    · rw [index]; dsimp [B] at lt; omega
  apply (loopFromBody (fun c => count - scanIndex c) body).conseq
  · intro c h
    change ScanAtWith writes a b count start initial (scanIndex c) c footprint expected
    rw [h.index_eq geometry]; exact h
  · intro c ⟨h, stop⟩
    have bound := h.upper
    have eq : scanIndex c = count := by dsimp [B] at stop; omega
    simpa only [I, eq] using h


/-- The original integer-only scan retains its stronger register frame. -/
theorem scan_loop {a b count start initial}
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (immediates : ∀ j, start ≤ j → j < count →
      guardB .BNE (word initial (a + 8 * j) &&& 1#64) 0 = true) :
    Triple (ScanAt a b count start initial start) (ScanAt a b count start initial count) := by
  apply ScanAtWith.loop geometry
  intro i c ⟨h, bound⟩
  exact scan_iteration geometry header immediates h bound

end OCaml.Vm.Gc.FieldCopy
