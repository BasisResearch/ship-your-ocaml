import OCaml.Vm.Primitives.GprsKeptCore
import OCaml.Vm.Sim.PinsPresence
import Vsa.Sim.StepFrameOut

/-! Register presence across a generated segment: its output pins cover what
it writes. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable OCaml.Vm.Primitives

/-- **A generated segment keeps register presence**: its output pins cover
every register it writes (one `decide`), and it does not write `gp`. -/
theorem GprsKept.of_segment {W : List Register} {L : List Pin} {before after : Config}
    (frame : StepFrameOut W before.σ after.σ) (pins : PinsHold after.σ L)
    (cover : ∀ r ∈ W, r ∈ noiseRegs ∨ (r ∈ L.map Sigma.fst ∧ r ≠ gprReg 3)) : GprsKept before after where
  present n lo hi h := by
    by_cases w : ∃ r ∈ W, (r == gprReg n) = true
    · obtain ⟨r, hr, eq⟩ := w
      have e : r = gprReg n := beq_iff_eq.mp eq
      subst e
      rcases cover _ hr with noise | ⟨mem, -⟩
      · exact absurd noise (by gpr_cases n => decide)
      · change (gprGet after.σ n).isSome
        gpr_cases n => exact pins.isSome_mem mem
    · simp only [not_exists, not_and, Bool.not_eq_true] at w
      change (gpr after n).isSome
      have keep : gpr after n = gpr before n := by
        unfold gpr
        gpr_cases n => exact frame.frame _ fun r hr => by simpa [gprReg] using w r hr
      rw [keep]; exact h
  gp := frame.frame (gprReg 3) fun r hr => by
    rcases cover r hr with noise | ⟨-, ne⟩
    · exact (by decide : ∀ q ∈ noiseRegs, (q == gprReg 3) = false) r noise
    · exact beq_false_of_ne ne

/-- The cover check of `GprsKept.of_segment`: reduce the pin list to its
registers (the values may be symbolic), then one `decide`. -/
macro "seg_cover" : tactic =>
  `(tactic| (simp only [List.map_cons, List.map_nil, Sigma.fst, List.forall_mem_append] <;>
    (repeat' apply And.intro) <;> decide))

end OCaml.Vm.Sim
