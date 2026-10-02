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

end Vsa.Densify
