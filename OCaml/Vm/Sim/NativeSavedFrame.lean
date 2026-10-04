import OCaml.Vm.Sim.ReadGeometry
import OCaml.Vm.Sim.LogRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- Callee-saved native registers at the offsets extracted from the prologue. -/
structure NativeSavedFrame (registers : List Nat) (offset : Nat → Nat) (nativeSp : Nat) (saved : Nat → BitVec 64) (c : Config) : Prop where
  words : ∀ r ∈ registers, word c (nativeSp + offset r) = saved r
  reads : ∀ r ∈ registers, RamReadAt (nativeSp + offset r) 8

/-- Runtime stores outside the saved native frame retain every return value. -/
theorem NativeSavedFrame.frame {registers : List Nat} {offset : Nat → Nat} {nativeSp : Nat} {saved : Nat → BitVec 64} {c after : Config} {log : List WEntry}
    (h : NativeSavedFrame registers offset nativeSp saved c)
    (outside : ∀ r ∈ registers, OutLRange log (nativeSp + offset r) 8)
    (memory : after.σ.mem = writeLog c.σ.mem log) : NativeSavedFrame registers offset nativeSp saved after := by
  refine ⟨?_, h.reads⟩
  intro r hr
  have same : word after (nativeSp + offset r) = word c (nativeSp + offset r) := by
    rw [word, memory]
    exact bytesT_writeLog_out c.σ.mem (outside r hr)
  exact same.trans (h.words r hr)

end OCaml.Vm.Sim
