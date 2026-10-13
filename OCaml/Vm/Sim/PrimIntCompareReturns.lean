import OCaml.Vm.Sim.CcallNames
import OCaml.Vm.Primitives.CamlIntCompare

/-! `caml_int_compare` at every `C_CALL` site: two int arguments, the
represented read-only summary. -/
namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem prim_caml_int_compare_returns {L : OCaml.Layout} {P : Prog} {op : Opcode} {ra : BitVec 64} {k : Nat}
    (stable : MemoryStable L.runtimeOk) :
    PrimReturnsAt L P op ra k "caml_int_compare" := by
  intro s c0 pl cp sp high table entry value env index v heap world reach ready sem _words
  obtain ⟨a, b, args⟩ : ∃ a b, s.accu :: s.stack.take k = [.int a, .int b] := by
    cases e : s.stack.take k with
    | nil => rw [e] at sem; simp [primF1Impl] at sem
    | cons y ys =>
      rw [e] at sem
      cases ys with
      | cons _ _ => simp [primF1Impl] at sem
      | nil =>
        cases hx : s.accu <;> cases y <;> rw [hx] at sem <;> simp [primF1Impl, intArg?] at sem
        exact ⟨_, _, rfl⟩
  have model : primF1Impl "caml_int_compare" [.int a, .int b] s.heap s.world =
      .ok (.int (compareResult a b)) s.heap s.world := rfl
  rw [args, model] at sem
  cases sem
  have hentry : entry = Layout.sym_caml_int_compare :=
    Option.some.inj (ready.entryName.symm.trans PrimitiveEntries.entry_caml_int_compare)
  subst hentry
  rw [args]
  exact ⟨_, ccall_callee_of_readOnly (writes := [10, 15]) (by decide) model (by decide) fun c input =>
    caml_int_compare_primitive stable a b input⟩

end OCaml.Vm.Sim
