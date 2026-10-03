import OCaml.Vm.Primitives.MemoryFrame
import OCaml.Vm.Primitives.Write
import OCaml.Vm.Primitives.ImageFrame
import Vsa.Sim.InterpSpillReads

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Total native word loads retain their value outside an exact write log. -/
theorem word_read_writeLog_out {c : Config} {a : Nat} {log : List WEntry}
    {memory : Std.ExtHashMap Nat (BitVec 8)}
    (outside : OutLRange log a 8) (written : memory = writeLog c.σ.mem log) :
    sign_extend (m := 64) (bytesT8 memory a) = word c a := by
  rw [written]
  simpa only [word, bytesT_eight_eq, sign_extend,
    Sail.BitVec.signExtend, BitVec.signExtend_eq] using bytesT_writeLog_out c.σ.mem outside

/-- Read a selected full-word store after all later, disjoint entries.
The existing spill-read certificate supplies the write-log observation. -/
theorem word_writeLog_at (m : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry)
    (i a : Nat) (w : BitVec 64) (selected : log[i]? = some (a, 8, w))
    (outside : OutLRange (log.drop (i + 1)) a 8) :
    bytesT (writeLog m log) a 8 = w := by
  have read := read64_of_writeLog_at m log i a w selected outside
  have value := execRetEpilogueWord_value _ _ w read
  change bytesVal .ld (read8 (writeLog m log) a) = w at value
  simpa only [read8_value] using value

/-- Configuration-level readback for a selected store in an exact memory log. -/
theorem word_after_writeLog_at {before after : Config} {log : List WEntry}
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (i a : Nat) (w : BitVec 64) (selected : log[i]? = some (a, 8, w))
    (outside : OutLRange (log.drop (i + 1)) a 8) : word after a = w := by
  rw [word, memory]
  exact word_writeLog_at _ _ i a w selected outside

/-- An outside-range certificate also covers any sub-log, such as a prefix. -/
theorem outLRange_sublist {small large : List WEntry} {a n : Nat}
    (sub : small.Sublist large) (outside : OutLRange large a n) : OutLRange small a n := by
  induction sub with
  | slnil => trivial
  | cons _ _ ih => exact ih outside.2
  | cons_cons _ _ ih => exact ⟨outside.1, ih outside.2⟩

/-- Global image separation also certifies each store or prefix of a log. -/
theorem imageOutside_sublist {small large : List WEntry}
    (sub : small.Sublist large) (outside : ImageOutside large) : ImageOutside small :=
  ⟨outLRange_sublist sub outside.text, outLRange_sublist sub outside.rodata⟩


end OCaml.Vm.Sim
