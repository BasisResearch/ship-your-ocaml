import OCaml.Vm.Sim.StackPayload

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Consuming an existing prefix advances the represented stack pointer. -/
theorem stack_drop {c : Config} {pl : Place} {sp high n : Nat} {stk : List Val}
    (h : StackRepr c pl sp high stk) (bound : n ≤ stk.length) :
    StackRepr c pl (sp + 8 * n) high (stk.drop n) := by
  constructor
  · simp only [List.length_drop]
    have shape := h.1
    omega
  · intro i v hv
    rw [List.getElem?_drop] at hv
    have slot := h.2 (n + i) v hv
    simpa only [Nat.mul_add, ← Nat.add_assoc] using slot

/-- Dropping stack roots cannot introduce new live heap locations. -/
theorem live_stack_drop {P : Prog} {s : St} {n l : Nat}
    (h : Live s.heap (roots P {s with stack := s.stack.drop n}) l) :
    Live s.heap (roots P s) l := by
  apply live_stack_of_root ?_ h
  intro v hv l hl
  exact Live.root (by simp [roots, List.mem_of_mem_drop hv]) hl

/-- Read-only stack consumption keeps the remaining payload and trap offset. -/
theorem payload_stack_drop {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high n : Nat} (h : VmPayload P s c pl cp sp high) (bound : n ≤ s.stack.length) :
    VmPayload P {s with stack := s.stack.drop n} c pl cp (sp + 8 * n) high := by
  apply payload_stack_of_root h ?_ (stack_drop h.stack bound)
  intro v hv l hl
  exact Live.root (by simp [roots, List.mem_of_mem_drop hv]) hl

end OCaml.Vm.Sim
