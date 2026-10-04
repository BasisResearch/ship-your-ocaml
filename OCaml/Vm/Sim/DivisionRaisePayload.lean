import OCaml.Vm.Sim.NativeReentry
import OCaml.Vm.Sim.StackDrop
import OCaml.Vm.Sim.FieldRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives LeanRV64DExecutable

/-- The logical pre-unwind state discards the divisor and selects the exception. -/
def divisionRaiseState (s : St) (exn : Val) : St := {s with accu := exn, stack := s.stack.drop 1}

/-- Selecting a predefined global exception and dropping the divisor introduces no new roots. -/
theorem division_raise_payload_before {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a k : Nat} {exn : Val}
    (h : VmPayload P s c pl cp sp high)
    (field : FieldSelection s.heap pl P.globals 5 exn l a k)
    (nonempty : 1 ≤ s.stack.length) :
    VmPayload P (divisionRaiseState s exn) c pl cp (sp + 8) high := by
  have observed := field.read_payload h (by simp [roots])
  have selected := h.accu_of_root exn observed.root
  exact payload_stack_drop selected nonempty

/-- The predefined exception and remaining logical stack survive a disjoint native log. -/
theorem division_raise_payload {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high l a k : Nat} {exn : Val} {log : List WEntry}
    (h : VmPayload P s c pl cp sp high)
    (field : FieldSelection s.heap pl P.globals 5 exn l a k)
    (nonempty : 1 ≤ s.stack.length)
    (outside : PayloadOutside log P (divisionRaiseState s exn) c pl cp (sp + 8)) :
    VmPayload P (divisionRaiseState s exn) (nativeMemoryView c log) pl cp (sp + 8) high :=
  (division_raise_payload_before h field nonempty).frame_log outside rfl rfl

/-- A final full-word store publishes the exception in the canonical native memory view. -/
theorem native_memory_last_word {c : Config} {log front : List WEntry} {address : Nat} {value : BitVec 64}
    (last : log = front ++ [(address, 8, value)]) :
    word (nativeMemoryView c log) address = value := by
  change bytesT (writeLog c.σ.mem log) address 8 = value
  rw [last, writeLog_append]
  exact word_writeLog _ _ _

end OCaml.Vm.Sim
