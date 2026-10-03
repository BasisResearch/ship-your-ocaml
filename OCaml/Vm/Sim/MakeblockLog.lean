import OCaml.Vm.Sim.MakeblockInput
import OCaml.Vm.Sim.MakeblockCopy

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Split the first initialized field from the generated forward copy. -/
theorem value_log_cons (a : Nat) (word : BitVec 64) (words : List (BitVec 64)) :
    valueLog a (word :: words) = (a, 8, word) :: valueLog (a + 8) words := by
  apply List.ext_getElem
  · simp only [value_log_length, List.length_cons]
  · intro i hi hj
    simp only [value_log_length, List.length_cons] at hi hj
    cases i with
    | zero => simp [value_log_getElem]
    | succ i =>
      have bound : i < words.length := by omega
      rw [value_log_getElem a (word :: words) (i + 1) (by simp only [List.length_cons]; omega),
        List.getElem_cons_succ, List.getElem_cons_succ,
        value_log_getElem (a + 8) words i bound]
      congr 1
      omega

def makeblockSetupLog (domain a count tag : Nat) (accu : BitVec 64) : List WEntry :=
  grabReserveLog domain a ++ [(a - 8, 8, blockHeader count tag), (a, 8, accu)]

/-- Machine initialization followed by the copy is the canonical block store log. -/
theorem makeblock_log_parts (c : Config) (sp count tag a domain : Nat) (accu : BitVec 64)
    (positive : 0 < count) :
    makeblockSetupLog domain a count tag accu ++ valueLog (a + 8) (stackWords c sp (count - 1)) =
      makeblockLog c sp count tag a domain accu := by
  have length : (makeblockWords c sp count accu).length = count := by
    simp only [makeblockWords, List.length_cons, stackWords, List.length_map, List.length_range]
    omega
  change (accu :: stackWords c sp (count - 1)).length = count at length
  simp only [makeblockLog, blockLog, makeblockWords, length, value_log_cons,
    makeblockSetupLog, List.append_assoc, List.cons_append, List.nil_append]

end OCaml.Vm.Sim
