import OCaml.Bytecode.Semantics

/-! Arity facts for the implemented F1 primitive model. Keeping these proofs
in a separate module avoids rebuilding semantics consumers when they evolve. -/

namespace OCaml.Bytecode
set_option autoImplicit false

/-- Every implemented F1 argument pattern has arity 1, 2 or 4. This covers
all primitive outcomes, including the unary `caml_sys_exit` pattern. -/
theorem primF1Impl_wrong_arity {name : String} {args : List Val} {h : Heap} {w : World}
    (one : args.length ≠ 1) (two : args.length ≠ 2) (four : args.length ≠ 4) :
    primF1Impl name args h w = .unsupported := by
  unfold primF1Impl
  split <;> simp_all

/-- A defined F1 outcome, whether return, exit, raise or callback, requires
one of the implemented arities. No primitive-table restriction is needed. -/
theorem primF1Impl_arity {name : String} {args : List Val} {h : Heap} {w : World}
    (defined : primF1Impl name args h w ≠ .unsupported) :
    args.length = 1 ∨ args.length = 2 ∨ args.length = 4 := by
  by_cases one : args.length = 1
  · exact Or.inl one
  by_cases two : args.length = 2
  · exact Or.inr (Or.inl two)
  by_cases four : args.length = 4
  · exact Or.inr (Or.inr four)
  exact (defined (primF1Impl_wrong_arity one two four)).elim

end OCaml.Bytecode
