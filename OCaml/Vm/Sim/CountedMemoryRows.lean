import OCaml.Vm.Sim.CountedRuntime
import OCaml.Vm.Sim.A2TableRows

/-! Initial ordinary counted rows through the shared generic runtime lift.
The existing generated/native opcode proofs are reused unchanged. -/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- CONST0 preserves complete accounting on its actual generic row. -/
theorem counted_const0_row {L : OCaml.Layout} {P : Prog}
    {Customs : Config → Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (stable : MemoryStable L.runtimeOk) (accounting : Gc.CustomAccounting Ready state Customs) :
    OCaml.OpArm P (CountedLoopAt Customs L P) .CONST0 := by
  apply counted_memory_row stable accounting (fun _ stable => const0_row stable)
  intro s i s' opcode effect
  obtain ⟨op, args⟩ := i
  simp only at opcode
  subst op
  cases args with
  | nil => cases Res.next.inj effect; rfl
  | cons a args => cases effect

/-- NEGINT uses the same runtime lift, including its existing integer guard. -/
theorem counted_negint_row {L : OCaml.Layout} {P : Prog}
    {Customs : Config → Nat → Prop} {Ready : Nat → Config → Prop} {state : Config → Nat → Prop}
    (stable : MemoryStable L.runtimeOk) (accounting : Gc.CustomAccounting Ready state Customs) :
    OCaml.OpArm P (CountedLoopAt Customs L P) .NEGINT := by
  apply counted_memory_row stable accounting (fun _ stable => negint_row stable)
  intro s i s' opcode effect
  obtain ⟨op, args⟩ := i
  simp only at opcode
  subst op
  cases args with
  | nil =>
    cases accu : s.accu <;> simp only [stepI, accu] at effect <;> cases effect <;> rfl
  | cons a args => cases effect

end OCaml.Vm.Sim
