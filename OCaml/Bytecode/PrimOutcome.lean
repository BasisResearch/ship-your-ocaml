import OCaml.Bytecode.Semantics

/-! The outcomes of the F1 primitives: none raises or calls back, and only
`caml_sys_exit` (one argument) exits. -/

namespace OCaml.Bytecode

theorem primF1Impl_ne_raise {name : String} {args : List Val} {h h' : Heap} {w w' : World} {e : Val} :
    primF1Impl name args h w ≠ .raise e h' w' := by
  intro hr
  unfold primF1Impl at hr
  split at hr <;> (try dsimp only at hr) <;> (repeat' split at hr) <;> simp_all [openChan]

theorem primF1Impl_ne_callback {name : String} {args cbargs : List Val} {h h' : Heap} {w w' : World}
    {f : Val} : primF1Impl name args h w ≠ .callback f cbargs h' w' := by
  intro hr
  unfold primF1Impl at hr
  split at hr <;> (try dsimp only at hr) <;> (repeat' split at hr) <;> simp_all [openChan]

theorem primF1Impl_exit {name : String} {args : List Val} {h : Heap} {w w' : World} {e : Nat}
    (hr : primF1Impl name args h w = .exit e w') : name = "caml_sys_exit" ∧ args.length = 1 := by
  unfold primF1Impl at hr
  split at hr <;> (try dsimp only at hr) <;> (repeat' split at hr) <;> simp_all [openChan]

end OCaml.Bytecode
