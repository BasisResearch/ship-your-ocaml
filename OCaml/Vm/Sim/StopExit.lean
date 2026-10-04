import OCaml.Vm.Sim.StopReturn
import OCaml.Run.Machine

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine

/-- The enclosing startup call must continue from the returned interpreter to
HTIF exit, preserving the represented world's output. Its generated caller and
process-exit summaries supply this obligation; STOP itself only returns. -/
structure StopExitContinuation (before : Config) (nativeSp : Nat) (saved : Nat → BitVec 64)
    (value vmSp : BitVec 64) (output : String) : Prop where
  resume : ∀ after, StopReturnPost before nativeSp saved value vmSp after → Halts after output 0

/-- Compose the proved STOP return with the explicitly named enclosing exit continuation. -/
theorem stop_halts {nativeSp : Nat} {saved : Nat → BitVec 64} {value vmSp : BitVec 64}
    {c : Config} {output : String} (h : StopInput nativeSp saved value vmSp c)
    (exit : StopExitContinuation c nativeSp saved value vmSp output) : Halts c output 0 := by
  obtain ⟨count, after, run, post⟩ := stop_return h
  obtain ⟨σ, halted, printed⟩ := OCaml.Run.vsa_halts_iff.mp (exit.resume after post)
  exact OCaml.Run.vsa_halts_iff.mpr ⟨σ,
    OCaml.Run.HaltsK.of_reach ⟨count, OCaml.Run.vsa_stepsN_iff.mp run⟩ halted, printed⟩

end OCaml.Vm.Sim
