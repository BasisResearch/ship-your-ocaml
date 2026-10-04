import OCaml.Vm.Sim.DivisionRaisePayload
import OCaml.Vm.Sim.DivisionCall
import OCaml.Vm.Sim.RaiseFrame

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A caught zero-divisor step is the shared handler state after selecting the predefined exception. -/
theorem division_zero_state (kind : DivisionKind) {P : Prog} {s s' : St} {x : BitVec 63}
    {tail rest : List Val} {exn env : Val} {dest : Nat} {link extra : BitVec 63}
    (accu : s.accu = .int x) (stack : s.stack = .int 0#63 :: tail)
    (field : field? s.heap P.globals 5 = some exn)
    (frame : RaiseFrame (divisionRaiseState s exn) dest link env extra rest)
    (step : stepI P s ⟨divisionOpcode kind, []⟩ = .next s') :
    {divisionRaiseState s exn with
      pc := dest, env := env, extra := extra.toNat,
      stack := rest, trap := s.trap - link.toNat} = s' := by
  have raised : raiseTo P {s with stack := tail} exn = .next s' := by
    cases kind <;> simpa [stepI, divisionOpcode, accu, stack, ints?, opt, field] using step
  have active : s.trap ≠ 0 := by have positive := frame.active; change 0 < s.trap at positive; omega
  have same : raiseTo P (divisionRaiseState s exn) exn = raiseTo P {s with stack := tail} exn := by
    simp only [raiseTo, divisionRaiseState, stack, List.drop_succ_cons, List.drop_zero, active, ite_false]
  exact frame.state_of_step (same.trans raised)

end OCaml.Vm.Sim
