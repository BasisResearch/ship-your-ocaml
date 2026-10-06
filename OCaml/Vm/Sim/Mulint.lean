import OCaml.Vm.Sim.MulintSetup
import OCaml.Run.Machine

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable
open OCaml.Vm.Primitives

/-- MULINT consumes the represented integer stack head through the actual
libgcc call. Read geometry and runtime framing remain
explicit obligations of the full loop invariant. -/
theorem mulint_arm {L : OCaml.Layout} {P : Prog} {s : OCaml.Bytecode.St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat} {m n : BitVec 63} {rest : List Val}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .MULINT c pl cp sp high)
    (accu : s.accu = .int m) (stack : s.stack = .int n :: rest)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8) :
    ∃ after, Plus c after ∧
      Running L P {s with pc := s.pc + 1, accu := .int (m * n), stack := rest} after := by
  have bound : 1 ≤ s.stack.length := by simp only [stack, List.length_cons]; omega
  have restore := consume_arm (pc := s.pc + 1) (count := 1) (n := m * n) stable h bound
  simp only [stack, List.drop_succ_cons, List.drop_zero, Nat.mul_one] at restore
  apply restore
  intro d dp
  obtain ⟨nb, call, steps, setup⟩ := mulint_setup h accu stack read dp
  have pre : Vsa.Logic.Triple (fun e => e = d) (MulintCall d pl (s.pc + 1) (sp + 8) m n) := by
    rintro e rfl
    exact ⟨call, steps.toSteps, setup⟩
  obtain ⟨after, run, post⟩ := (callSeg pre mulint_callee mulint_return) d rfl
  exact ⟨_, after, run.toN_of_stepsField, post⟩

/-- The real successful bytecode transition supplies MULINT's integer inputs. -/
theorem mulint_step_arm {L : OCaml.Layout} {P : Prog} {s s' : OCaml.Bytecode.St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high : Nat}
    (stable : MemoryStable L.runtimeOk)
    (h : ArmInput L P s .MULINT c pl cp sp high)
    (read : ReadWindow (BitVec.ofNat 64 sp) 8)
    (step : stepI P s ⟨.MULINT, []⟩ = .next s') :
    ∃ after, Plus c after ∧ Running L P s' after := by
  have step' : intOp s (fun a b => tag64 (untag a * untag b)) = .next s' := step
  obtain ⟨m, n, rest, accu, stack, state⟩ := intOp_next step'
  simp only [untag_tag] at state
  rw [← state]
  exact mulint_arm stable h accu stack read

end OCaml.Vm.Sim
