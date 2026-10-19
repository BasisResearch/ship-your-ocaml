import OCaml.Vm.Sim.CcallNames

/-! `caml_sys_exit` at every `C_CALL` site: it never returns, so its returning
summary is vacuous (its exit is `CcallExit`, lane bprime). -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode

/-- `caml_sys_exit` never returns normally. -/
theorem primF1Impl_sys_exit_ne_ok {args : List Val} {h h' : Heap} {w w' : World} {v : Val} :
    primF1Impl "caml_sys_exit" args h w ≠ .ok v h' w' := by
  intro hr
  unfold primF1Impl at hr
  split at hr <;> (try dsimp only at hr) <;> (repeat' split at hr) <;> simp_all [openChan]

theorem prim_caml_sys_exit_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat} :
    PrimReturnsAt L P op ra k "caml_sys_exit" := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sem _
  exact (primF1Impl_sys_exit_ne_ok sem).elim

end OCaml.Vm.Sim
