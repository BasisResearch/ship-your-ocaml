import OCaml.Vm.Sim.CcallNames

/-!
# C_CALL summaries of primitives with too many arguments

At a `C_CALLk` site the primitive receives `accu :: stack.take k`, at most
`k + 1` arguments. A primitive whose model needs more never returns there,
so its summary at that site is vacuous (`PrimReturnsAtR.of_short`).
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- **A primitive that needs more than `k + 1` arguments has a vacuous
summary at a `C_CALLk` site.** -/
theorem PrimReturnsAtR.of_short {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    {name : String}
    (never : ∀ (args : List Val) (h : Heap) (w : World) (v : Val) (h' : Heap) (w' : World),
      args.length ≤ k + 1 → primF1Impl name args h w = .ok v h' w' → False) :
    PrimReturnsAtR L P op ra k name := by
  intro s c pl cp sp high table entry value env index v heap world _ _ ok _ _
  exact (never _ _ _ _ _ _ (by simp only [List.length_cons, List.length_take]; omega) ok).elim

/-- The model's arity check, for one primitive name and at most `k + 1`
arguments: unfold the argument list and evaluate `primF1Impl`. -/
macro "prim_short" : tactic => `(tactic| (
  intro args h w v h' w' len ok
  rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, rest⟩⟩⟩⟩⟩⟩ <;>
    simp_all [primF1Impl]))

end OCaml.Vm.Sim
