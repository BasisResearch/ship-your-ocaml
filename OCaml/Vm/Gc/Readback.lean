import OCaml.Vm.Primitives.Write
import Vsa.Sim.InterpSpillReads

namespace OCaml.Vm.Gc
open Vsa.Sim Primitives

/-- Read back any full-word store whose suffix is disjoint, using the existing
write-log read64 theorem and the shared total-read bridge. -/
theorem word_writeLog_at (mem : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (i a : Nat) (v : BitVec 64)
    (entry : log[i]? = some (a, 8, v))
    (outside : OutLRange (log.drop (i + 1)) a 8) :
    bytesT (writeLog mem log) a 8 = v := by
  have read := read64_of_writeLog_at mem log i a v entry outside
  have value := execRetEpilogueWord_value _ _ v read
  change bytesVal .ld (read8 (writeLog mem log) a) = v at value
  simpa only [read8_value] using value

end OCaml.Vm.Gc
