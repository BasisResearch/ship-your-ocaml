import OCaml.Vm.Gc.MixedScan
import OCaml.Vm.Gc.ScanPayload

namespace OCaml.Vm.Gc.FieldCopy
open OCaml.Bytecode Vsa.Machine Vsa.Sim Primitives Reloc

/-- NoForgery handles nonpointers; the placement/heap invariant must separately
show that genuine pointer fields need no young-pointer oldification. -/
theorem pending_nonYoung {q : PendingCopy} {fields : List Val} {pl initial P s domain}
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (safe : NoForgery P s pl (Young.lowerWord domain initial).toNat (Young.upperWord domain initial).toNat)
    (scanned : ∀ (i : Nat) v, fields[i]? = some v → 1 ≤ i → Scanned P s v)
    (stablePointers : ∀ (i : Nat) v w, fields[i]? = some v → 1 ≤ i → v.loc? ≠ none →
      valWord pl v = some w → ¬ YoungWord (Young.lowerWord domain initial).toNat
        (Young.upperWord domain initial).toNat w) :
    ∀ j, 1 ≤ j → j < fields.length → (word initial (q.source.toNat + 8 * j)).toNat % 2 = 0 →
      ¬ ((Young.lowerWord domain initial).toNat < (word initial (q.source.toNat + 8 * j)).toNat ∧
        (word initial (q.source.toNat + 8 * j)).toNat < (Young.upperWord domain initial).toNat) := by
  intro j lower bound even
  have hj : fields[j]? = some fields[j] := List.getElem?_eq_getElem bound
  have represented : valWord pl fields[j] = some (word initial (q.source.toNat + 8 * j)) := by
    have zero : j ≠ 0 := by omega
    simpa [Eqv.val, zero] using grey j fields[j] hj
  have notYoung : ¬ YoungWord (Young.lowerWord domain initial).toNat
      (Young.upperWord domain initial).toNat (word initial (q.source.toNat + 8 * j)) := by
    by_cases nonpointer : (fields[j]).loc? = none
    · exact safe _ _ (scanned j fields[j] hj lower) nonpointer represented
    · exact stablePointers j fields[j] _ hj lower nonpointer represented
  intro bounds
  exact notYoung ⟨even, Nat.le_of_lt bounds.1, bounds.2⟩

/-- Mixed copied suffix with a represented final block under the unchanged
placement. This does not cover fields pointing into the nursery. -/
structure MixedGreyPost (q : PendingCopy) (fields : List Val) (pl : Place)
    (cp : ChanPlace) (tag : Nat) (initial c : Config) : Prop where
  scan : ScanAtWith copyWrites q.source.toNat q.target.toNat fields.length 1 initial fields.length c
  object : ObjAt c pl cp q.target.toNat (.block tag fields)

/-- A mixed immediate/old-pointer payload is scanned by the actual loop,
using NoForgery for every represented nonpointer and explicit pointer stability. -/
theorem scan_mixed_grey {q : PendingCopy} {fields : List Val} {pl cp tag initial P s domain}
    (geometry : Geometry q.source.toNat q.target.toNat fields.length)
    (header : HeaderOk (word initial (q.target.toNat - 8)) fields.length tag)
    (grey : (pendingPayload q fields).P pl q.target.toNat initial)
    (runtime : DomainFrame domain q.target.toNat 1 fields.length initial)
    (safe : NoForgery P s pl (Young.lowerWord domain initial).toNat (Young.upperWord domain initial).toNat)
    (scanned : ∀ (i : Nat) v, fields[i]? = some v → 1 ≤ i → Scanned P s v)
    (stablePointers : ∀ (i : Nat) v w, fields[i]? = some v → 1 ≤ i → v.loc? ≠ none →
      valWord pl v = some w → ¬ YoungWord (Young.lowerWord domain initial).toNat
        (Young.upperWord domain initial).toNat w) :
    Vsa.Logic.Triple (ScanAtWith copyWrites q.source.toNat q.target.toNat fields.length 1 initial 1)
      (MixedGreyPost q fields pl cp tag initial) := by
  apply (mixed_scan geometry header.2 runtime (pending_nonYoung grey safe scanned stablePointers)).conseq
  · exact fun _ h => h
  · intro c h
    exact ⟨h, h.object geometry header grey⟩

end OCaml.Vm.Gc.FieldCopy
