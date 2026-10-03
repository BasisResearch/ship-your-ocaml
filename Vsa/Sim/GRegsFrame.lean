import Vsa.Sim.SegToTripleFramed

namespace Vsa.Sim
open Vsa.Machine LeanRV64DExecutable

/-- Join independently established finite register observations. -/
theorem gholds_append {σ : MState} (xs ys : GRegs) :
    GHolds σ (xs ++ ys) ↔ GHolds σ xs ∧ GHolds σ ys := by
  induction xs with
  | nil => simp [GHolds]
  | cons pin rest ih => simp only [List.cons_append, GHolds, ih, and_assoc]

/-- Select a finite interface from reflected register observations. -/
theorem gholds_select {σ : MState} {L : GRegs} (holds : GHolds σ L)
    (wanted : GRegs)
    (select : ∀ n v, (n, v) ∈ wanted → lookupG n L = some v) : GHolds σ wanted := by
  induction wanted with
  | nil => trivial
  | cons pin rest ih =>
    rcases pin with ⟨n, v⟩
    exact ⟨gholds_lookup _ holds (select n v (List.mem_cons_self ..)),
      ih (fun n v h => select n v (List.mem_cons_of_mem _ h))⟩

/-- Transport a selected register interface through the segment kernel's
complete frame. This shares the finite-register adapter across call seams. -/
theorem gholds_of_frame {before after : MState} {writes : List Nat}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) →
      after.regs.get? r = before.regs.get? r)
    (L : GRegs) (keys : KeysOK (keysG L))
    (noise : ∀ n ∈ keysG L, ∀ q ∈ noiseRegs, (q == gprReg n) = false)
    (outside : ∀ n ∈ keysG L, ∀ m ∈ writes, (gprReg m == gprReg n) = false)
    (holds : GHolds before L) : GHolds after L := by
  induction L with
  | nil => trivial
  | cons pin rest ih =>
    rcases pin with ⟨n, v⟩
    have member : n ∈ keysG ((n, v) :: rest) := List.mem_cons_self ..
    have bound := keys n member
    refine ⟨(gprGet_of_frame n bound.1 bound.2 (noise n member) (outside n member) frame).trans holds.1, ?_⟩
    exact ih (fun n hn => keys n (List.mem_cons_of_mem _ hn))
      (fun n hn => noise n (List.mem_cons_of_mem _ hn))
      (fun n hn => outside n (List.mem_cons_of_mem _ hn)) holds.2

/-- Two states satisfying the same finite pin list agree on every listed key. -/
theorem gholds_key_eq {before after : MState} {L : GRegs} {n : Nat}
    (beforePins : GHolds before L) (afterPins : GHolds after L) (member : n ∈ keysG L) :
    gprGet after n = gprGet before n := by
  induction L with
  | nil => cases member
  | cons cell rest ih =>
      rcases cell with ⟨k,v⟩
      rcases List.mem_cons.mp member with same | tail
      · subst n
        exact afterPins.1.trans beforePins.1.symm
      · exact ih beforePins.2 afterPins.2 tail

/-- Convert a typed GPR equality back into the machine's dependent register
view. The finite register split is shared here, not repeated at call sites. -/
theorem regGet_of_gprGet_eq {before after : MState} (n : Nat)
    (lower : 1 ≤ n) (upper : n ≤ 31) (same : gprGet after n = gprGet before n) :
    after.regs.get? (gprReg n) = before.regs.get? (gprReg n) := by
  gpr_cases n => exact same

/-- Shrink a native clobber set using registers restored to their original
values. This is the shared ABI-frame adapter for complete generated callees. -/
theorem frame_of_restored {before after : MState} {writes clobbers : List Nat}
    (frame : ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ writes, (gprReg n == r) = false) → after.regs.get? r = before.regs.get? r)
    (L : GRegs) (keys : KeysOK (keysG L))
    (beforePins : GHolds before L) (afterPins : GHolds after L)
    (cover : ∀ n ∈ writes, n ∈ clobbers ∨ n ∈ keysG L) :
    ∀ r : Register, (∀ q ∈ noiseRegs, (q == r) = false) →
      (∀ n ∈ clobbers, (gprReg n == r) = false) → after.regs.get? r = before.regs.get? r := by
  classical
  intro r noise outside
  by_cases untouched : ∀ n ∈ writes, (gprReg n == r) = false
  · exact frame r noise untouched
  · obtain ⟨n, bad⟩ := Classical.not_forall.mp untouched
    have member : n ∈ writes := by
      by_cases h : n ∈ writes
      · exact h
      · exact False.elim (bad (fun hn => False.elim (h hn)))
    have notFalse : ¬ (gprReg n == r) = false := fun h => bad (fun _ => h)
    have equal : gprReg n = r := by simpa using notFalse
    have restored : n ∈ keysG L := (cover n member).resolve_left (fun hn => notFalse (outside n hn))
    subst r
    exact regGet_of_gprGet_eq n (keys n restored).1 (keys n restored).2
      (gholds_key_eq beforePins afterPins restored)

end Vsa.Sim
