import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Primitives.CamlSysArgv

/-! `caml_sys_argv` at every `C_CALL` site: the `main_argv` word, which the
payload binds to `world.argv` (`VmPayload.argv`). -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem prim_caml_sys_argv_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_sys_argv" := by
  intro s c0 pl cp sp high table entry value env index v heap world _reach ready sem _words
  have nil : s.stack.take k = [] := by
    cases e : s.stack.take k with
    | nil => rfl
    | cons _ _ => rw [e] at sem; simp [primF1Impl] at sem
  rw [nil] at sem ⊢
  have model : primF1Impl "caml_sys_argv" [s.accu] s.heap s.world = .ok s.world.argv s.heap s.world := rfl
  rw [model] at sem
  cases sem
  have hentry : entry = Layout.sym_caml_sys_argv :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_sys_argv)
  subst hentry
  exact ⟨(valWord pl s.world.argv).getD 0, ccall_callee_of_readOnly (writes := [10]) (by decide) model (by decide)
    fun c input => by
      have argv := input.data.argv
      have e : (valWord pl s.world.argv).getD 0 = word c Layout.sym_main_argv := by rw [argv]; rfl
      rw [e]
      exact caml_sys_argv_primitive stable input argv⟩

end OCaml.Vm.Sim
