import OCaml.Vm.Sim.StackPush

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- A represented finite front joins the existing stack at its exact end.
Return frames and application frames share this word-indexing proof. -/
theorem stack_prepend {c : Config} {pl : Place} {start sp high : Nat}
    {front tail : List Val} (stack : StackRepr c pl sp high tail)
    (join : start + 8 * front.length = sp)
    (values : ∀ i v, front[i]? = some v → valWord pl v = some (word c (start + 8 * i))) :
    StackRepr c pl start high (front ++ tail) := by
  constructor
  · simp only [List.length_append, Nat.mul_add]
    have shape := stack.1
    omega
  · intro i v hv
    by_cases first : i < front.length
    · rw [List.getElem?_append_left first] at hv
      exact values i v hv
    · rw [List.getElem?_append_right (by omega)] at hv
      have address : start + 8 * i = sp + 8 * (i - front.length) := by omega
      rw [address]
      exact stack.2 _ _ hv

/-- Add a frame containing only old roots, after its writes have been checked.
The payload/root transport is the existing stack-change abstraction. -/
theorem payload_stack_prepend {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {start sp high : Nat} {front : List Val}
    (payload : VmPayload P s c pl cp sp high)
    (join : start + 8 * front.length = sp)
    (values : ∀ i v, front[i]? = some v → valWord pl v = some (word c (start + 8 * i)))
    (root : ∀ v ∈ front, ∀ l, v.loc? = some l → Live s.heap (roots P s) l) :
    VmPayload P {s with stack := front ++ s.stack} c pl cp start high := by
  apply payload_stack_of_root payload ?_ (stack_prepend payload.stack join values)
  intro v hv l hl
  rcases List.mem_append.mp hv with first | old
  · exact root v first l hl
  · exact Live.root (by simp [roots, old]) hl

end OCaml.Vm.Sim
