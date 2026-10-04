import OCaml.Vm.Sim.SignedDivisionState

namespace OCaml.Vm.Sim
set_option autoImplicit false
open Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The shared core has computed both unsigned results; only sign restoration
and the actual wrapper return remain. -/
structure SignedDivisionDivided (kind : DivisionKind) (before : Config) (x y ra : BitVec 64)
    (after : Config) : Prop
    extends LeafInput (divisionReturn kind x y ra) after where
  pc : pcOf after = some (divisionReturn kind x y ra)
  quotientReg : gpr after 10 = some (divisionMagnitude x / divisionMagnitude y)
  remainderReg : gpr after 11 = some (divisionMagnitude x % divisionMagnitude y)
  returnAligned : ra.toNat % 4 = 0
  savedReturn : kind = .remainder ∨ divisionNegative kind x y = true → gpr after 5 = some ra
  memory : after.σ.mem = before.σ.mem
  frame : StepFrameOut divisionWrites before.σ after.σ

/-- Both wrappers consume the same total unsigned-core summary. -/
theorem signed_division_core {kind : DivisionKind} {before c : Config} {x y ra : BitVec 64}
    (h : SignedDivisionPrepared kind before x y ra c) :
    ∃ after, Steps c after ∧ SignedDivisionDivided kind before x y ra after := by
  obtain ⟨after, run, post⟩ := (udivdi3_summary h.toUdivdi3Input).run c ⟨h.pc, rfl⟩
  have frame : StepFrameOut divisionWrites c.σ after.σ := by
    refine ⟨post.output, ?_⟩
    intro r hr
    apply post.frame r
    exact ⟨hr Register.x10 (by decide),
      hr Register.x11 (by decide),
      hr Register.x12 (by decide),
      hr Register.x13 (by decide),
      hr Register.PC (by decide),
      hr Register.nextPC (by decide),
      hr Register.minstret (by decide),
      hr Register.minstret_increment (by decide),
      hr Register.mcycle (by decide),
      hr Register.mtime (by decide),
      hr Register.mip (by decide)⟩
  refine ⟨after, run, post.toLeafInput, post.pc, post.quotientReg, post.remainderReg,
    h.returnAligned, ?_, post.memory.trans h.memory,
    (h.frame.trans frame).widenChecked (allowed := divisionWrites) (by decide)⟩
  intro needed
  exact (post.frame Register.x5 (by decide)).trans (h.savedReturn needed)

/-- For a nonnegative quotient the core already returned to the caller. -/
theorem signed_division_done {before c : Config} {x y ra : BitVec 64}
    (h : SignedDivisionDivided .quotient before x y ra c)
    (positive : divisionNegative .quotient x y = false) :
    SignedDivisionPost before ra (divisionResult .quotient x y) c := by
  refine ⟨h.good, h.image, h.minstret, h.tick, ?_, ?_, h.memory, h.frame⟩
  · simpa only [divisionReturn, positive, Bool.false_eq_true, ite_false] using h.pc
  · rw [division_result_sign, positive]
    exact h.quotientReg

end OCaml.Vm.Sim
