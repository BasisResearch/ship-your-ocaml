import OCaml.Vm.Sim.GrabReserve
import OCaml.Vm.Sim.GrabFinish

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- The actual G1 allocating GRAB path, through reservation, initialization,
arbitrary-count argument copy, and saved caller-frame restoration. -/
theorem grab_alloc_arm {L : OCaml.Layout} {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit dest : Nat} {env : BitVec 64}
    {required : BitVec 32} {savedEnv : Val} {savedExtra : BitVec 63} {rest : List Val}
    (runtime : AllocationRuntime L.runtimeOk c (grabAllocationLog c pl s sp a domain env))
    (h : ArmInput L P s .GRAB c pl cp sp high) (operand : OperandAt P pl (s.pc + 1) required)
    (short : s.extra < required.toInt.toNat) (environment : valWord pl s.env = some env)
    (stack : s.stack.drop (1 + s.extra) = .code dest :: savedEnv :: .int savedExtra :: rest)
    (savedNonnegative : 0 ≤ savedExtra.toInt)
    (space : GrabAllocInput P s c pl cp sp high a domain limit env) :
    ∃ after, Plus c after ∧ Running L P (grabState s dest savedEnv savedExtra rest) after := by
  apply dispatch_compose h.dispatch
  intro d dp
  obtain ⟨nr, reserved, reserveSteps, reservation⟩ := grab_reserve h operand short space.nursery dp
  obtain ⟨ni, middle, initSteps, front⟩ := grab_initialize h environment space.nursery space.initializer reservation
  obtain ⟨copied, copySteps, back⟩ := cursor_copy_run (space.initializer.copy_after front) middle front.copy
  obtain ⟨nf, after, finishSteps, running⟩ := grab_finish runtime h environment stack savedNonnegative space front back
  have setupRun : Steps d middle := OCaml.Run.vsa_steps_iff.mpr
    ⟨nr + ni, OCaml.Run.vsa_stepsN_iff.mp (reserveSteps.append initSteps)⟩
  have finishRun : Steps copied after := OCaml.Run.vsa_steps_iff.mpr ⟨nf, OCaml.Run.vsa_stepsN_iff.mp finishSteps⟩
  obtain ⟨n, whole⟩ := (setupRun.trans (copySteps.trans finishRun)).toN
  exact ⟨n, after, whole, running⟩

/-- Successful insufficient-arity GRAB agrees with the represented closure
allocation and caller state. Geometry and nursery preservation stay explicit. -/
theorem grab_alloc_step_arm {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high a domain limit dest : Nat} {env : BitVec 64}
    {required : BitVec 32} {savedEnv : Val} {savedExtra : BitVec 63} {rest : List Val}
    (runtime : AllocationRuntime L.runtimeOk c (grabAllocationLog c pl s sp a domain env))
    (h : ArmInput L P s .GRAB c pl cp sp high) (operand : OperandAt P pl (s.pc + 1) required)
    (short : s.extra < required.toInt.toNat) (environment : valWord pl s.env = some env)
    (stack : s.stack.drop (1 + s.extra) = .code dest :: savedEnv :: .int savedExtra :: rest)
    (savedNonnegative : 0 ≤ savedExtra.toInt)
    (space : GrabAllocInput P s c pl cp sp high a domain limit env)
    (step : stepI P s ⟨.GRAB, [required.toInt]⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have insufficient : ¬ required.toInt.toNat ≤ s.extra := by omega
  have valid : ¬ (s.stack.length < (1 + s.extra) + 3 ∨ s.pc < 1) := by
    have lengths := congrArg List.length stack
    simp only [List.length_drop, List.length_cons] at lengths
    have positive := space.pcPositive
    omega
  have state : grabState s dest savedEnv savedExtra rest = s' := by
    simpa only [stepI, insufficient, valid, ite_false, stack, grabClosure, grabState,
      List.cons_append, List.nil_append, Res.next.injEq] using step
  rw [← state]
  exact grab_alloc_arm runtime h operand short environment stack savedNonnegative space

end OCaml.Vm.Sim
