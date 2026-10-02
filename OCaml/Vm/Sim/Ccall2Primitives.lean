import OCaml.Vm.Sim.Ccall2
import OCaml.Vm.Primitives.CamlIntCompare

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim
open OCaml.Vm.Primitives

/-- The landed integer-comparison primitive supplies the binary call's
represented returning-callee contract. No primitive execution is reproved. -/
theorem c_call2_int_compare_callee {L : OCaml.Layout} {P : Prog} {s : St}
    {pl : Place} {cp : ChanPlace} {sp high domain : Nat} {env : BitVec 64}
    (stable : MemoryStable L.runtimeOk) (a b : BitVec 63)
    (accu : s.accu = .int a) (stack : s.stack[0]? = some (.int b)) :
    CcallCallee (0x80003004#64) (s.accu :: s.stack.take 1)
      L P s pl cp sp high domain Layout.sym_caml_int_compare env
      "caml_int_compare" (.int (compareResult a b)) (tag64 (compareResult a b)) s.heap s.world := by
  have args : s.accu :: s.stack.take 1 = [.int a, .int b] := by
    cases hs : s.stack with
    | nil => simp [hs] at stack
    | cons x xs =>
      have value : x = .int b := by simpa [hs] using stack
      simp [accu, value]
  refine ccall_callee_of_readOnly (writes := [10, 15]) (by decide) ?_ (by decide) ?_
  · rw [args]
    rfl
  · intro c input
    rw [args] at input ⊢
    exact caml_int_compare_primitive stable a b input

end OCaml.Vm.Sim
