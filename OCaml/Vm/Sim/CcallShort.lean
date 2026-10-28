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

/-- Shared operand and wrong-arity argument for a fixed-arity C_CALL.
Malformed operands, negative indices, short stacks and absent primitive
slots follow the actual stepI rejection branches. Only after its depth
check does `accu :: stack.take k` have exactly `k + 1` arguments.
An absent slot is `.wrong` (opt none); other rejected branches are
`.unsupported`, including every selected F1 primitive at this arity. -/
theorem ccall_wrong_arity_step {P : Prog} {op : Opcode} {k : Nat}
    (one : k + 1 ≠ 1) (two : k + 1 ≠ 2) (four : k + 1 ≠ 4)
    (semantics : ∀ s args, stepI P s ⟨op, args⟩ = match args with
      | [p] => if p < 0 ∨ s.stack.length < k then .unsupported else
          opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: s.stack.take k)
      | _ => .unsupported)
    (ccallName : ∀ p : Int, Instr.ccallName P ⟨op, [p]⟩ = P.prims[p.toNat]?)
    {s : St} {args : List Int} (f1 : OCaml.InF1 P ⟨op, args⟩) :
    stepI P s ⟨op, args⟩ = .unsupported ∨ stepI P s ⟨op, args⟩ = .wrong := by
  simp only [semantics]
  rcases args with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · exact Or.inl rfl
  · change (if p < 0 ∨ s.stack.length < k then .unsupported else
      opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: s.stack.take k)) = .unsupported ∨ _
    by_cases guard : p < 0 ∨ s.stack.length < k
    · exact Or.inl (by simp only [guard, ite_true])
    simp only [guard, ite_false]
    cases slot : P.prims[p.toNat]? with
    | none => exact Or.inr rfl
    | some name =>
        apply Or.inl
        have member : name ∈ primsF1 := f1.prim (by rw [ccallName, slot])
        have length : (s.accu :: s.stack.take k).length = k + 1 := by
          simp only [List.length_cons, List.length_take]
          omega
        have rejected := primF1Impl_wrong_arity (name := name) (h := s.heap) (w := s.world)
          (by omega : (s.accu :: s.stack.take k).length ≠ 1)
          (by omega : (s.accu :: s.stack.take k).length ≠ 2)
          (by omega : (s.accu :: s.stack.take k).length ≠ 4)
        simp only [opt, cCall, prim, primF1, member, ite_true, rejected]
  · exact Or.inl rfl

/-- A complete row over any loop relation when the real F1 semantics
reject every operand shape. No native return or exit supplier is required. -/
theorem ccall_wrong_arity_row {P : Prog} {op : Opcode} {k : Nat}
    {R : St → Config → Prop}
    (one : k + 1 ≠ 1) (two : k + 1 ≠ 2) (four : k + 1 ≠ 4)
    (semantics : ∀ s args, stepI P s ⟨op, args⟩ = match args with
      | [p] => if p < 0 ∨ s.stack.length < k then .unsupported else
          opt P.prims[p.toNat]? fun nm => cCall P s 2 nm (s.accu :: s.stack.take k)
      | _ => .unsupported)
    (ccallName : ∀ p : Int, Instr.ccallName P ⟨op, [p]⟩ = P.prims[p.toNat]?) :
    OCaml.OpArm P R op := by
  intro s c i _ _ _ opcode f1
  obtain ⟨o, args⟩ := i
  cases opcode
  rcases ccall_wrong_arity_step one two four semantics ccallName f1 with rejected | rejected <;>
    rw [rejected] <;> trivial

end OCaml.Vm.Sim
