import OCaml.Vm.Gc.ChainPlan
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.Word32Access

/-!
# Support lemmas for generated chain modules

`scripts/gen_chain.py` emits one module per straight route through generated
rows: per-block register and log lemmas, access plans and a named `Route`.
A load that follows stores in the same block reads the block's threaded
symbolic memory; these two lemmas carry its byte pins back to the
block-start memory, one instruction at a time.
-/

namespace OCaml.Vm.Gc
open Vsa.Sim Vsa.Machine OCaml.Vm.Primitives

/-- The kinds the block evaluator treats as stores. -/
def storeKind : MKind → Bool
  | .sw | .sd | .sb | .sh => true
  | _ => false

/-- A non-store instruction leaves the block's symbolic memory unchanged. -/
theorem lpins8_stepMemM_keep {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} {x : Nat}
    {bs : List (BitVec 8)} (h : storeKind a.kind = false) (pins : LPins8 m x bs) :
    LPins8 (stepMemM m a L) x bs := by
  unfold stepMemM
  split <;> simp_all [storeKind]

/-- A doubleword store apart from the load keeps the load's byte pins. -/
theorem lpins8_stepMemM_apart {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} {x : Nat}
    {y : BitVec 64} {bs : List (BitVec 8)} (h : a.kind = .sd) (address : eaddrM a L = y)
    (pins : LPins8 m x bs) (apart : x + 8 ≤ y.toNat ∨ y.toNat + 8 ≤ x) :
    LPins8 (stepMemM m a L) x bs := by
  have out : OutLRange [wentryM a L] x 8 :=
    ⟨by simp only [wentryM, widthOfM, h, address]; omega, trivial⟩
  have := lpins8_writeLog pins out
  simpa [stepMemM, h, writeLog] using this

theorem lpins4_stepMemM_keep {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} {x : Nat}
    {bs : List (BitVec 8)} (h : storeKind a.kind = false) (pins : LPins4 m x bs) :
    LPins4 (stepMemM m a L) x bs := by
  unfold stepMemM
  split <;> simp_all [storeKind]

theorem lpins4_stepMemM_apart {m : Std.ExtHashMap Nat (BitVec 8)} {a : MInstr} {L : GRegs} {x : Nat}
    {y : BitVec 64} {bs : List (BitVec 8)} (h : a.kind = .sd) (address : eaddrM a L = y)
    (pins : LPins4 m x bs) (apart : x + 4 ≤ y.toNat ∨ y.toNat + 8 ≤ x) :
    LPins4 (stepMemM m a L) x bs := by
  have out : OutLRange [wentryM a L] x 4 :=
    ⟨by simp only [wentryM, widthOfM, h, address]; omega, trivial⟩
  have := lpins4_writeLog pins out
  simpa [stepMemM, h, writeLog] using this

end OCaml.Vm.Gc
