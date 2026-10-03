import Vsa.Machine
open Vsa.Machine LeanRV64DExecutable
namespace Vsa.Sim
/-- The remaining sequential-state components have singleton types. -/
theorem state_eq (s t : MState) (regs : s.regs = t.regs) (mem : s.mem = t.mem)
    (cycles : s.cycleCount = t.cycleCount) (output : s.sailOutput = t.sailOutput) : s = t := by
  cases s
  cases t
  cases regs
  cases mem
  cases cycles
  cases output
  congr
/-- A write inside a declared footprint preserves every register outside it. -/
theorem register_insert_frame (writes : List Register) (r : Register) (outside : r ∉ writes)
    (rs : Std.ExtDHashMap Register RegisterType) (q : Register) (v : RegisterType q)
    (inside : q ∈ writes) : (rs.insert q v).get? r = rs.get? r := by
  have ne : q ≠ r := fun eq => outside (eq ▸ inside)
  simp [Std.ExtDHashMap.get?_insert, ne]
end Vsa.Sim
