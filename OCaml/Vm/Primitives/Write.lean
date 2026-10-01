import OCaml.Vm.Primitives.Read
import Vsa.Sim.LibraryLoadValue

namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim

/-- Ordinary RAM stores are aligned and lie beyond the HTIF registers. -/
structure WriteWindow (a : BitVec 64) (width : Nat) : Prop where
  lower : 0x80000000 ≤ a.toNat
  upper : a.toNat + width ≤ 0x100000000
  htif : Layout.sym_tohost + 16 ≤ a.toNat
  aligned : a.toNat % width = 0

theorem WriteWindow.sd {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs}
    {a : MInstr} {x : BitVec 64} {bs : List (BitVec 8)} (h : WriteWindow x 8)
    (kind : a.kind = .sd) (address : eaddrM a L = x) : MemFacts m L bs a := by
  simp only [MemFacts, kind, address]
  refine ⟨h.lower, h.upper, ?_, h.aligned⟩
  simpa only [tohostAddr, LibraryLayout.tohostAddr, Layout.sym_tohost] using h.htif

/-- Observe the value stored by one full-word write-log entry. -/
theorem word_writeLog (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (value : BitVec 64) :
    bytesT (writeLog m [(a, 8, value)]) a 8 = value := by
  have hr := read64_writeMap8 m a (sdData_val value)
  rw [sdData_toNat] at hr
  have hv := execRetEpilogueWord_value _ _ value hr
  change bytesVal .ld (read8 (writeLog m [(a, 8, value)]) a) = value at hv
  simpa only [read8_value] using hv

/-- Runtime predicates may ignore changes inside a designated write window. -/
def WindowStable (runtimeOk : Config → Prop) (windows : List W) : Prop :=
  ∀ c c', FrameOn windows c.σ.mem c'.σ.mem → runtimeOk c → runtimeOk c'

end OCaml.Vm.Primitives
