import OCaml.Vm.Sim.MakeblockInput
import OCaml.Vm.Sim.MakeblockCopy

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

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
