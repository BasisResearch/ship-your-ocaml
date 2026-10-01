import Vsa.Sim.Boot.Log

/-! Balanced composition of small packed-log certificates. -/
namespace Vsa.Sim.Boot

/-- Store checks over a half-open interval of log indices. -/
structure StoresChecked (L : PackedLog) (t : RunTree) (lo hi : Nat) : Prop where
  checks : ∀ i, lo ≤ i → i < hi → storeOk L t i = true

theorem StoresChecked.chunk {L : PackedLog} {t : RunTree} {lo n : Nat}
    (h : storesIn L t lo n = true) : StoresChecked L t lo (lo + n) :=
  ⟨fun _ hlo hi => storesIn_spec h hlo hi⟩

theorem StoresChecked.join {L : PackedLog} {t : RunTree} {lo mid hi : Nat}
    (left : StoresChecked L t lo mid) (right : StoresChecked L t mid hi) :
    StoresChecked L t lo hi where
  checks := by
    intro i hlo hhi
    by_cases hm : i < mid
    · exact left.checks i hlo hm
    · exact right.checks i (by omega) hhi

/-- Every final-byte run in a tree has a checked writer. -/
structure RunTree.Checked (L : PackedLog) (t : RunTree) : Prop where
  checks : ∀ r ∈ t.runs, runOk L r r.len = true

theorem RunTree.Checked.leaf {L : PackedLog} {r : Run}
    (h : runOk L r r.len = true) : Checked L (.leaf r) where
  checks := by
    intro s hs
    obtain rfl := List.mem_singleton.mp hs
    exact h

theorem RunTree.Checked.node {L : PackedLog} {l r : RunTree} {pivot : Nat}
    (left : Checked L l) (right : Checked L r) : Checked L (.node pivot l r) where
  checks := fun s hs => (List.mem_append.mp hs).elim (left.checks s) (right.checks s)

/-- Assemble the two independently chunked sides of the existing log checker. -/
theorem LogOk.of_checks {L : PackedLog} {t : RunTree}
    (stores : StoresChecked L t 0 L.len) (runs : RunTree.Checked L t) : LogOk L t :=
  ⟨fun i hi => stores.checks i (Nat.zero_le _) hi, runs.checks⟩

end Vsa.Sim.Boot
