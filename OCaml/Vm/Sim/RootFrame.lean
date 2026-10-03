import OCaml.Vm.Primitives.Payload

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- Restrict a represented heap to a state with the same objects and no new
live locations. Root-edit adapters share placement and separation transport. -/
theorem heap_of_live {P : Prog} {s target : St} {c : Config} {pl : Place} {cp : ChanPlace}
    (h : HeapRepr c pl cp P s) (heap : target.heap = s.heap)
    (live : ∀ l, Live target.heap (roots P target) l → Live s.heap (roots P s) l) :
    HeapRepr c pl cp P target := by
  constructor
  · intro l hl
    simpa only [heap] using h.1 l (live l hl)
  · intro l l' a a' o o' hl hl' hn hp hp' hg hg'
    rw [heap] at hg hg'
    exact h.2 l l' a a' o o' (live l hl) (live l' hl') hn hp hp' hg hg'

/-- Replacing the environment by an existing root retains the live heap. -/
theorem live_env_of_root {P : Prog} {s : St} {env : Val} {l : Nat}
    (root : ∀ l, env.loc? = some l → Live s.heap (roots P s) l)
    (h : Live s.heap (roots P {s with env := env}) l) : Live s.heap (roots P s) l := by
  apply live_of_roots h
  intro v loc member address
  rcases List.mem_cons.mp member with rfl | member
  · exact Live.root (by simp [roots]) address
  rcases List.mem_cons.mp member with rfl | member
  · exact root loc address
  · exact Live.root (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)) address

/-- Function entry and return may select an already represented environment. -/
theorem payload_env_of_root {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (env : Val)
    (root : ∀ l, env.loc? = some l → Live s.heap (roots P s) l) :
    VmPayload P {s with env := env} c pl cp sp high := by
  exact {h with heap := heap_of_live h.heap rfl (fun _ hl => live_env_of_root root hl)}

/-- Extra-argument counts do not occur in the memory payload or root graph. -/
theorem payload_extra {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} (h : VmPayload P s c pl cp sp high) (extra : Nat) :
    VmPayload P {s with extra := extra} c pl cp sp high := by
  exact {h with}

end OCaml.Vm.Sim
