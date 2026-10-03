import OCaml.Vm.Sim.RootFrame
import OCaml.Vm.Sim.StackDrop
import OCaml.Vm.Sim.ReadOnly

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine OCaml.Vm.Primitives

/-- A return selects its environment while all old roots are still present,
then removes the consumed stack prefix and restores PC/extra arguments. -/
theorem return_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high count pc extra : Nat} {env : Val}
    (h : VmPayload P s c pl cp sp high) (bound : count ≤ s.stack.length)
    (root : ∀ l, env.loc? = some l → Live s.heap (roots P s) l) :
    VmPayload P {s with pc := pc, env := env, extra := extra, stack := s.stack.drop count}
      c pl cp (sp + 8 * count) high := by
  exact payload_pc (payload_extra (payload_stack_drop (payload_env_of_root h env root) bound) extra) pc

end OCaml.Vm.Sim
