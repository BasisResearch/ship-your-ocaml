import OCaml.Vm.Sim.StackAcc

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Changing the stack to already live roots cannot introduce a new heap location. -/
theorem live_stack_of_root {P : Prog} {s : St} {stack : List Val} {l : Nat}
    (root : ∀ v ∈ stack, ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (h : Live s.heap (roots P {s with stack := stack}) l) :
    Live s.heap (roots P s) l := by
  apply live_of_roots h
  intro v loc hv hl
  simp only [roots, List.mem_cons, List.mem_append] at hv
  rcases hv with (((hv | hv | hv | hv | hv) | hv) | hv) | hv <;>
    first | exact root v hv loc hl | exact Live.root (by simp [roots, hv]) hl


/-- One heap-root restriction for all stack edits made from already live values.
The caller separately supplies the new stack's concrete words and shape. -/
theorem payload_stack_of_root {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp sp' high : Nat} {stack : List Val} (h : VmPayload P s c pl cp sp high)
    (root : ∀ v ∈ stack, ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (words : StackRepr c pl sp' high stack) :
    VmPayload P {s with stack := stack} c pl cp sp' high := by
  refine { h with stack := words, heap := ?_ }
  constructor
  · intro l hl
    exact h.heap.1 l (live_stack_of_root root hl)
  · intro l l' a a' o o' hl hl' hn hp hp' hg hg'
    exact h.heap.2 l l' a a' o o' (live_stack_of_root root hl)
      (live_stack_of_root root hl') hn hp hp' hg hg'

end OCaml.Vm.Sim
