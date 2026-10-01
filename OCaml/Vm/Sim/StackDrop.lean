import OCaml.Vm.Sim.StackAcc

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
  apply live_of_roots h
  intro v loc hv hl
  apply Live.root ?_ hl
  simp only [roots, List.mem_cons, List.mem_append] at hv ⊢
  rcases hv with hv | hv
  · apply Or.inl
    rcases hv with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (List.mem_of_mem_drop h))))
  · exact Or.inr hv

/-- Read-only stack consumption keeps the remaining payload and trap offset. -/
theorem payload_stack_drop {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high n : Nat} (h : VmPayload P s c pl cp sp high) (bound : n ≤ s.stack.length) :
    VmPayload P {s with stack := s.stack.drop n} c pl cp (sp + 8 * n) high := by
  refine { h with stack := stack_drop h.stack bound, heap := ?_ }
  constructor
  · intro l hl
    exact h.heap.1 l (live_stack_drop hl)
  · intro l l' a a' o o' hl hl' hn hp hp' hg hg'
    exact h.heap.2 l l' a a' o o' (live_stack_drop hl) (live_stack_drop hl') hn hp hp' hg hg'

end OCaml.Vm.Sim
