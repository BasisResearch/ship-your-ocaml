import OCaml.Vm.Sim.StackEdit
import OCaml.Vm.Sim.StackPrefix
import OCaml.Vm.Sim.PayloadRestore
import OCaml.Vm.Sim.LogWindow

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Replace a stack prefix with represented words, retaining the untouched
suffix. Fixed application frames and tail-call argument moves share this proof. -/
theorem payload_replace_prefix {P : Prog} {s : St} {before after : Config}
    {pl : Place} {cp : ChanPlace} {sp start high count : Nat} {front : List Val} {log : List WEntry}
    (h : VmPayload P s before pl cp sp high) (bound : count ≤ s.stack.length)
    (outside : StackEditOutside log P s before pl cp high)
    (inside : LogInW [⟨start, sp + 8 * count⟩] log)
    (memory : after.σ.mem = writeLog before.σ.mem log)
    (out : after.σ.sailOutput = before.σ.sailOutput)
    (join : start + 8 * front.length = sp + 8 * count)
    (values : ∀ i v, front[i]? = some v → valWord pl v = some (word after (start + 8 * i)))
    (root : ∀ v ∈ front, ∀ l, v.loc? = some l → Live s.heap (roots P s) l) :
    VmPayload P {s with stack := front ++ s.stack.drop count} after pl cp start high := by
  have tail : StackRepr after pl (sp + 8 * count) high (s.stack.drop count) := by
    apply stack_frame_log (stack_drop h.stack bound) _ memory
    intro i v selected
    apply outLRange_of_windows inside
    simp only [OutWRange, and_true]
    omega
  apply payload_frame_stack h outside memory out _ (stack_prepend tail join values)
  intro v member l loc
  rcases List.mem_append.mp member with first | old
  · exact root v first l loc
  · exact Live.root (by simp [roots, List.mem_of_mem_drop old]) loc

end OCaml.Vm.Sim
