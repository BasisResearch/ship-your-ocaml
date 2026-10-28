import Vsa.Sim.BlockMem
import Vsa.Densify.Resp

namespace Vsa.Densify
open Vsa.Sim

/-- Scalar symbolic stores respect the machine's total-byte observations. -/
theorem MemEqv.applyW {m m'} (h : MemEqv m m') (entry : WEntry) :
    MemEqv (applyW m entry) (applyW m' entry) := by
  rcases entry with ⟨a, width, value⟩
  unfold Vsa.Sim.applyW
  split <;> try simp only [writeMap4, writeMap8]
  all_goals repeat' apply MemEqv.insert
  all_goals exact h

/-- A first-order write log can be composed after an observational library
frame without claiming equality of optional memory maps. -/
theorem MemEqv.writeLog {m m'} (h : MemEqv m m') (log : List WEntry) :
    MemEqv (writeLog m log) (writeLog m' log) := by
  induction log generalizing m m' with
  | nil => exact h
  | cons entry rest ih => exact ih (h.applyW entry)

/-- Inserting the same byte preserves agreement at a selected observation. -/
theorem insert_observed_at {m m' : Std.ExtHashMap Nat (BitVec 8)} {x a : Nat} {b : BitVec 8}
    (same : (m[x]?).getD 0 = (m'[x]?).getD 0) :
    ((m.insert a b)[x]?).getD 0 = ((m'.insert a b)[x]?).getD 0 := by
  simp only [Std.ExtHashMap.getElem?_insert]
  split <;> first | rfl | exact same

/-- Scalar stores depend on the incoming map only at the selected byte.
This permits partial observational frames across later allocation stores. -/
theorem applyW_observed_at {m m' : Std.ExtHashMap Nat (BitVec 8)} (entry : WEntry) {x : Nat}
    (same : (m[x]?).getD 0 = (m'[x]?).getD 0) :
    ((applyW m entry)[x]?).getD 0 = ((applyW m' entry)[x]?).getD 0 := by
  rcases entry with ⟨a, width, value⟩
  unfold applyW
  split <;> (try simp only [writeMap4, writeMap8])
  all_goals repeat' apply insert_observed_at
  all_goals exact same

/-- A first-order log transports agreement at any selected byte, even if
incoming memories differ elsewhere. No optional-map equality is inferred. -/
theorem writeLog_observed_at {m m' : Std.ExtHashMap Nat (BitVec 8)} (log : List WEntry) {x : Nat}
    (same : (m[x]?).getD 0 = (m'[x]?).getD 0) :
    ((writeLog m log)[x]?).getD 0 = ((writeLog m' log)[x]?).getD 0 := by
  induction log generalizing m m' with
  | nil => exact same
  | cons entry rest ih => exact ih (applyW_observed_at entry same)

end Vsa.Densify
