import OCaml.Vm.Sim.CcallNames

/-!
# C_CALL summaries of primitives called at the wrong arity

At a `C_CALLk` site whose stack holds the call's arguments, the primitive
receives `accu :: stack.take k`, exactly `k + 1` arguments. A primitive whose
model (`primF1Impl`) takes no `k + 1` arguments never returns there, so its
summary at that site is vacuous (`PrimReturnsAtD.of_arity`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **A primitive that takes no `k + 1` arguments has a vacuous summary at a
`C_CALLk` site.** -/
theorem PrimReturnsAtD.of_arity {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    {name : String}
    (never : ∀ (args : List Val) (h : Heap) (w : World) (v : Val) (h' : Heap) (w' : World),
      args.length = k + 1 → primF1Impl name args h w = .ok v h' w' → False) :
    PrimReturnsAtD L P op ra k name := by
  intro s c pl cp sp high table entry value env index v heap world _ depth _ ok _ _
  exact (never _ _ _ _ _ _ (by simp only [List.length_cons, List.length_take]; omega) ok).elim

/-- The model's arity check, for one primitive name and `k + 1` arguments:
unfold the argument list and evaluate `primF1Impl`. -/
macro "prim_arity" : tactic => `(tactic| (
  intro args h w v h' w' len ok
  rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, rest⟩⟩⟩⟩⟩⟩ <;>
    simp_all [primF1Impl]))

end OCaml.Vm.Sim
