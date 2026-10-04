import OCaml.Vm.Sim.ClosurerecRestore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

/-- A successful recursive-closure bytecode step agrees with the native
constructor's abstract object and reversed stack of interior pointers. -/
theorem closurerec_state_of_step {P : Prog} {s s' : St} {nf nv : Int}
    {offsets : List Int} {dest : Nat} {targets : List Nat}
    (arity : nf.toNat = targets.length + 1)
    (offsetCount : offsets.length = nf.toNat)
    (bound : nv.toNat - 1 ≤ s.stack.length)
    (jumps : offsets.mapM (fun o => target s.pc 2 o) = some (dest :: targets))
    (step : stepI P s ⟨.CLOSUREREC, nf :: nv :: offsets⟩ = .next s') :
    closurerecState s nv.toNat dest targets = s' := by
  have valid : ¬ (targets.length + 1 = 0 ∨ offsets.length ≠ targets.length + 1) := by omega
  have enough : ¬ (if 0 < nv.toNat then s.accu :: s.stack else s.stack).length < nv.toNat := by
    split
    · simp only [List.length_cons]; omega
    · omega
  simpa only [stepI, valid, enough, ite_false, jumps, opt, arity,
    closure_capture_stack, closure_stack_remaining, closurerecState, closurerecObject,
    closurerecFunctionValues, closurerecFunctionGroup, closurerecStack, St.adv,
    List.length_cons, Nat.add_assoc, Int.ofNat_eq_natCast, Res.next.injEq] using step

end OCaml.Vm.Sim
