import OCaml.Vm.Gc.ForwardedScan

namespace OCaml.Vm.Gc.MopupCall
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- The native save interval is extracted from the generated save slots. -/
def nativeWindow (R : Nat → BitVec 64) : W :=
  ⟨(OldifyEntry.frameSp R).toNat,
    (OldifyEntry.frameSp R).toNat + OldifyEntry.maxSlot.2 + 8⟩

def scanFootprint (R : Nat → BitVec 64) (b start count : Nat) : List W :=
  nativeWindow R :: FieldCopy.scanWindow b start count

/-- Every actual callee write is in the native save interval or is the
single destination store. Saved-register values play no role in separation. -/
theorem effect_entry_of_bound {R c b i}
    (bound : (OldifyEntry.frameSp R).toNat + OldifyEntry.maxSlot.2 + 8 ≤ 0x100000000)
    (destination : (R 11).toNat = b + 8 * i)
    {e : WEntry} (member : e ∈ ForwardedCall.effect R c) :
    ((nativeWindow R).lo ≤ e.1 ∧ e.1 + e.2.1 ≤ (nativeWindow R).hi) ∨
      (e.1 = b + 8 * i ∧ e.2.1 = 8) := by
  simp only [ForwardedCall.effect, List.mem_append, List.mem_singleton] at member
  rcases member with saved | root
  · obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp saved
    have addr := OldifyEntry.saved_address bound hc
    have offset := OldifyEntry.slots_bounded cell hc
    left
    change (nativeWindow R).lo ≤ (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat ∧
      (OldifyEntry.frameSp R + BitVec.ofNat 64 cell.2).toNat + 8 ≤ (nativeWindow R).hi
    rw [addr]
    change (OldifyEntry.frameSp R).toNat ≤ (OldifyEntry.frameSp R).toNat + cell.2 ∧
      (OldifyEntry.frameSp R).toNat + cell.2 + 8 ≤
        (OldifyEntry.frameSp R).toNat + OldifyEntry.maxSlot.2 + 8
    omega
  · subst e
    exact Or.inr ⟨destination, rfl⟩

/-- The suffix JAL changes only the saved return value, not save addresses. -/
theorem effect_entry {R c b i}
    (bound : (OldifyEntry.frameSp (linked R)).toNat + OldifyEntry.maxSlot.2 + 8 ≤ 0x100000000)
    (destination : (R 11).toNat = b + 8 * i)
    {e : WEntry} (member : e ∈ ForwardedCall.effect (linked R) c) :
    ((nativeWindow R).lo ≤ e.1 ∧ e.1 + e.2.1 ≤ (nativeWindow R).hi) ∨
      (e.1 = b + 8 * i ∧ e.2.1 = 8) :=
  effect_entry_of_bound bound destination member

/-- A natural interval description supplies all header and scanned-prefix
separation obligations. The native frame is disjoint from the whole object,
including its header; the current destination follows the scanned prefix. -/
theorem scanFootprint_of_geometry {R c a b count start i}
    (geometry : FieldCopy.Geometry a b count) (lower : start ≤ i) (upper : i < count)
    (bound : (OldifyEntry.frameSp (linked R)).toNat + OldifyEntry.maxSlot.2 + 8 ≤ 0x100000000)
    (target : R 19 = BitVec.ofNat 64 b)
    (destination : (R 11).toNat = b + 8 * i)
    (stack : (nativeWindow R).hi ≤ b - 8 ∨ b + 8 * count ≤ (nativeWindow R).lo) :
    ScanFootprint R c (scanFootprint R b start count) b start i := by
  have entries := fun e he => effect_entry (c := c) bound destination (e := e) he
  refine ⟨?_, ?_, ?_⟩
  · apply logInW_of_forall
    intro e member
    rcases entries e member with saved | ⟨address,width⟩
    · exact Or.inl saved
    · right
      change ((b + 8 * start ≤ e.1 ∧ e.1 + e.2.1 ≤ b + 8 * count) ∨ False)
      rw [address, width]
      exact Or.inl ⟨by omega, by omega⟩
  · rw [target, FieldCopy.header_nat geometry.targetRange]
    apply outLRange_of_forall
    intro e member
    have min := geometry.targetRange.lower
    rcases entries e member with saved | ⟨address,width⟩
    · rcases stack with before | after
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · rw [address, width]
      exact Or.inl (by omega)
  · intro j _ previous
    apply outLRange_of_forall
    intro e member
    rcases entries e member with saved | ⟨address,width⟩
    · rcases stack with before | after
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
    · rw [address, width]
      exact Or.inl (by omega)

end OCaml.Vm.Gc.MopupCall
