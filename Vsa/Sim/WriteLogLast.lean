import Vsa.Sim.WriteLogNF

namespace Vsa.Sim

/-- A final eight-byte store establishes the root word regardless of preceding
writes, including overlapping writes. Reuses the write-log and Pin8 laws. -/
theorem pin8_of_last_write (mem : Std.ExtHashMap Nat (BitVec 8)) (log : List WEntry)
    (addr : Nat) (value : BitVec 64) (last : log.getLast? = some (addr, 8, value)) :
    Pin8 (writeLog mem log) addr value := by
  obtain ⟨before, rfl⟩ := List.getLast?_eq_some_iff.mp last
  rw [writeLog_append]
  exact Pin8_writeMap8 (writeLog mem before) addr value

end Vsa.Sim
