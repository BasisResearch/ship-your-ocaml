import Vsa.Sim.RegPins
import Vsa.Sim.GprCases
import Vsa.Sim.BlockPilot

/-! Presence of registers pinned by a generated segment's output pins. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim LeanRV64DExecutable

/-- A pinned register is present. -/
theorem _root_.Vsa.Sim.PinsHold.isSome_mem {σ : MState} {L : List Pin} (h : PinsHold σ L)
    {r : Register} (hr : r ∈ L.map Sigma.fst) : (σ.regs.get? r).isSome := by
  induction L with
  | nil => cases hr
  | cons p rest ih =>
    rcases List.mem_cons.1 hr with e | hr
    · subst e; rw [h.1]; rfl
    · exact ih h.2 hr

/-- The written GPRs of a segment are present by its output pins. -/
theorem written_of_pins {σ : MState} {L : List Pin} (h : PinsHold σ L) {writes : List Nat}
    (cover : ∀ n ∈ writes, 1 ≤ n ∧ n ≤ 31 ∧ gprReg n ∈ L.map Sigma.fst) :
    ∀ n ∈ writes, (gprGet σ n).isSome := by
  intro n hn
  obtain ⟨h1, h31, hm⟩ := cover n hn
  gpr_cases n => exact h.isSome_mem hm

end OCaml.Vm.Sim
