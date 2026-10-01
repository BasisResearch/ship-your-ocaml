import OCaml.Vm.Sim.Immediate
import OCaml.Vm.Primitives.Read

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine

/-- Loading an existing stack value introduces no new heap root. -/
theorem stack_value_root {P : Prog} {s : St} {i : Nat} {v : Val}
    (selected : s.stack[i]? = some v) :
    ∀ l, v.loc? = some l → Live s.heap (roots P s) l := by
  intro l hl
  exact Live.root (by simp [roots, List.mem_of_getElem? selected]) hl

/-- Stack shape and the represented machine stack-high word exclude address
wraparound for every selected slot. RAM/HTIF geometry is separate. -/
theorem stack_slot_nat {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high i : Nat} {v : Val} (h : VmReprAt P s c pl cp sp high)
    (selected : s.stack[i]? = some v) :
    (BitVec.ofNat 64 (sp + 8 * i)).toNat = sp + 8 * i := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp selected
  have shape := h.stack.1
  have upper : high < 2^64 := by
    rw [← h.stackHigh]
    exact (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).isLt
  exact Nat.mod_eq_of_lt (by omega)

end OCaml.Vm.Sim
