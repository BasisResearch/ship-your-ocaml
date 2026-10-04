import OCaml.Vm.Primitives.Boundary
import Vsa.Sim.GRegsFrame
namespace OCaml.Vm.Primitives
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- Carry a finite register interface through a public summary frame. All
register exclusion checks remain finite certificates at the call site. -/
theorem holds_frame_ne {before after : MState} {writes : List Nat} {L : GRegs}
    (frame : ∀ r : Register, (∀ n ∈ writes, gprReg n ≠ r) →
      (∀ q ∈ noiseRegs, (q == r) = false) → after.regs.get? r = before.regs.get? r)
    (holds : GHolds before L) (keys : KeysOK (keysG L))
    (noise : ∀ n ∈ keysG L, ∀ q ∈ noiseRegs, (q == gprReg n) = false)
    (outside : ∀ n ∈ keysG L, ∀ m ∈ writes, (gprReg m == gprReg n) = false) :
    GHolds after L :=
  gholds_of_frame (fun r hn hw => frame r (fun n h => beq_eq_false_iff_ne.mp (hw n h)) hn)
    L keys noise outside holds
end OCaml.Vm.Primitives
