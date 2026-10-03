import OCaml.Vm.Gc.ScanLoop
import OCaml.Vm.Gc.CopyNonYoung

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Vsa.Logic LeanRV64DExecutable

/-- The destination suffix is disjoint from the three runtime words consulted
by Is_young. Heap/domain separation supplies these footprint facts. -/
structure DomainFrame (domain : BitVec 64) (b start count : Nat) (initial : Config) : Prop where
  register : gprGet initial.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  root : word initial Layout.sym_Caml_state = domain
  windows : Young.Windows domain
  rootOutside : Layout.sym_Caml_state + 8 ≤ b + 8 * start ∨ b + 8 * count ≤ Layout.sym_Caml_state
  lowerOutside : (domain + BitVec.ofNat 64 Layout.off_young_start).toNat + 8 ≤ b + 8 * start ∨
    b + 8 * count ≤ (domain + BitVec.ofNat 64 Layout.off_young_start).toNat
  upperOutside : (domain + BitVec.ofNat 64 Layout.off_young_end).toNat + 8 ≤ b + 8 * start ∨
    b + 8 * count ≤ (domain + BitVec.ofNat 64 Layout.off_young_end).toNat

structure DomainAt (domain : BitVec 64) (initial c : Config) : Prop where
  register : gprGet c.σ 22 = some (BitVec.ofNat 64 Layout.sym_Caml_state)
  root : word c Layout.sym_Caml_state = domain
  lower : Young.lowerWord domain c = Young.lowerWord domain initial
  upper : Young.upperWord domain c = Young.upperWord domain initial

theorem DomainFrame.at {domain a b start count initial i c}
    (runtime : DomainFrame domain b start count initial)
    (scan : ScanAtWith copyWrites a b count start initial i c) : DomainAt domain initial c := by
  refine ⟨?_, (word_frame scan.memory runtime.rootOutside).trans runtime.root, ?_, ?_⟩
  · have same : gprGet c.σ 22 = gprGet initial.σ 22 :=
      scan.native Register.x22 (by decide) (by decide)
    exact same.trans runtime.register
  · exact word_frame scan.memory runtime.lowerOutside
  · exact word_frame scan.memory runtime.upperOutside

/-- One concrete copy iteration: odd words take the immediate path; even
words outside the nursery take both real range tests before the shared store. -/
theorem mixed_iteration {domain a b count start initial i c}
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (runtime : DomainFrame domain b start count initial)
    (safeFields : ∀ j, start ≤ j → j < count → (word initial (a + 8 * j)).toNat % 2 = 0 →
      ¬ ((Young.lowerWord domain initial).toNat < (word initial (a + 8 * j)).toNat ∧
        (word initial (a + 8 * j)).toNat < (Young.upperWord domain initial).toNat))
    (h : ScanAtWith copyWrites a b count start initial i c) (bound : i < count) :
    ∃ d, Steps c d ∧ ScanAtWith copyWrites a b count start initial (i + 1) d := by
  let slot := scanPtr a i
  let delta := BitVec.ofNat 64 b - BitVec.ofNat 64 a
  let target := BitVec.ofNat 64 b
  let index := BitVec.ofNat 64 i
  have source : word c slot.toNat = word initial (a + 8 * i) := by
    rw [geometry.sourceRange.ptr_nat (Nat.le_of_lt bound)]
    apply word_frame h.memory
    have separate := geometry.separate
    omega
  have atHead : PCAt pc c := by simpa [bound] using h.pc
  have current := runtime.at h
  have safe : (word c slot.toNat).toNat % 2 = 0 →
      ¬ ((Young.lowerWord domain c).toNat < (word c slot.toNat).toNat ∧
        (word c slot.toNat).toNat < (Young.upperWord domain c).toNat) := by
    intro even
    rw [current.lower, current.upper, source]
    exact safeFields i h.lower bound (by rw [← source]; exact even)
  have input : ReadInput slot delta target index c :=
    ⟨h.good, h.minstret, h.tick, h.code, h.registers, geometry.sourceRange.window bound⟩
  obtain ⟨d, run, post⟩ := (copy_nonYoung input current.register current.root runtime.windows safe
    (geometry.windows bound).destination (geometry.windows bound).header).run c ⟨atHead, rfl⟩
  exact ⟨d, run, h.advance geometry header bound post⟩

/-- Complete mixed scan of fields requiring no young-pointer oldification.
The actual branch choice is recomputed for every field; no parity partition
of the program or branch oracle is assumed. -/
theorem mixed_scan {domain a b count start initial}
    (geometry : Geometry a b count)
    (header : (word initial (b - 8)).toNat / 1024 = count)
    (runtime : DomainFrame domain b start count initial)
    (safeFields : ∀ j, start ≤ j → j < count → (word initial (a + 8 * j)).toNat % 2 = 0 →
      ¬ ((Young.lowerWord domain initial).toNat < (word initial (a + 8 * j)).toNat ∧
        (word initial (a + 8 * j)).toNat < (Young.upperWord domain initial).toNat)) :
    Triple (ScanAtWith copyWrites a b count start initial start)
      (ScanAtWith copyWrites a b count start initial count) := by
  apply ScanAtWith.loop geometry
  intro i c ⟨h, bound⟩
  exact mixed_iteration geometry header runtime safeFields h bound

end OCaml.Vm.Gc.FieldCopy
