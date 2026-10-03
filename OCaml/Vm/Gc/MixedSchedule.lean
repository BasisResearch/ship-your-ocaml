import OCaml.Vm.Gc.MixedLoopState

namespace OCaml.Vm.Gc.MixedField
open Vsa.Machine Vsa.Sim Primitives LeanRV64DExecutable

/-- Predicted return register: copies retain it; a forwarded young field
sets it to the suffix JAL link. This is arithmetic on initial observations. -/
def returnAt (R : Nat → BitVec 64) (domain : BitVec 64) (a start : Nat) (initial : Config) : Nat → BitVec 64
  | 0 => R 1
  | i + 1 => if i < start then R 1 else
      if needsOldify domain (word initial (scanPtr a i).toNat) initial
      then MopupCall.call.link else returnAt R domain a start initial i

/-- Canonical maps for the mixed-loop data interface. No future machine
register value appears in this definition. -/
def schedule (R : Nat → BitVec 64) (domain : BitVec 64) (a start : Nat) (initial : Config)
    (i n : Nat) : BitVec 64 :=
  if n = 1 then returnAt R domain a start initial i
  else if n = 8 then scanPtr a i else if n = 9 then BitVec.ofNat 64 i else R n

theorem returnAt_before {R domain a start initial i} (before : i ≤ start) :
    returnAt R domain a start initial i = R 1 := by
  cases i with
  | zero => rfl
  | succ i => simp only [returnAt, ite_eq_left (show i < start by omega)]

theorem schedule_initial {R domain a start initial}
    (slot : R 8 = scanPtr a start) (index : R 9 = BitVec.ofNat 64 start) :
    schedule R domain a start initial start = R := by
  funext n
  by_cases one : n = 1
  · subst n; simp only [schedule, ite_true, returnAt_before (Nat.le_refl start)]
  by_cases eight : n = 8
  · subst n; simp [schedule, ← slot]
  by_cases nine : n = 9
  · subst n; simp [schedule, ← index]
  simp only [schedule, ite_eq_right one, ite_eq_right eight, ite_eq_right nine]

/-- The canonical maps discharge the mixed-loop transition premise. -/
theorem schedule_advance {R domain a start initial i} (lower : start ≤ i) :
    schedule R domain a start initial (i + 1) =
      next (schedule R domain a start initial i)
        (decide (needsOldify domain (word initial (scanPtr a i).toNat) initial)) := by
  funext n
  by_cases young : needsOldify domain (word initial (scanPtr a i).toNat) initial
  all_goals by_cases one : n = 1
  all_goals first
    | (subst n; simp [schedule, returnAt, next, ForwardedField.next, FieldCopy.copyNext,
        young, show ¬ i < start by omega])
    | skip
  all_goals by_cases eight : n = 8
  all_goals first
    | (subst n; simp [schedule, next, ForwardedField.next, FieldCopy.copyNext, young, scanPtr_succ])
    | skip
  all_goals by_cases nine : n = 9
  all_goals first
    | (subst n; simp [schedule, next, ForwardedField.next, FieldCopy.copyNext, young, BitVec.ofNat_add])
    | skip
  all_goals simp [schedule, next, ForwardedField.next, FieldCopy.copyNext, young, one, eight, nine]

end OCaml.Vm.Gc.MixedField
