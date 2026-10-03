import OCaml.Vm.Sim.EnterReady
import OCaml.Vm.Sim.LogRead
import OCaml.Vm.Sim.StackEdit
import OCaml.Vm.Sim.FieldRead

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions
open OCaml.Vm.Primitives

/-- Fixed-arity frame writes must preserve the shared application-tail checks. -/
structure EnterOutside (log : List WEntry) (c : Config) : Prop where
  domain : OutLRange log Layout.sym_Caml_state 8
  threshold : OutLRange log ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold) 8
  pending : OutLRange log Layout.sym_caml_something_to_do 4

/-- A partial frame-write log preserves every shared-tail read as well. -/
theorem EnterOutside.sublist {small large : List WEntry} {c : Config}
    (h : EnterOutside large c) (sub : small.Sublist large) : EnterOutside small c :=
  ⟨outLRange_sublist sub h.domain, outLRange_sublist sub h.threshold, outLRange_sublist sub h.pending⟩

/-- Pending-work reads remain zero after any separated frame-write prefix. -/
theorem SignalCheckReady.read_log {c : Config} {memory : Std.ExtHashMap Nat (BitVec 8)} {log : List WEntry}
    (quiet : SignalCheckReady c) (outside : OutLRange log Layout.sym_caml_something_to_do 4)
    (written : memory = writeLog c.σ.mem log) :
    sign_extend (m := 64) (bytesT4 memory Layout.sym_caml_something_to_do) = 0#64 := by
  have same := bytesT_writeLog_out c.σ.mem outside
  have clear : bytesT4 memory Layout.sym_caml_something_to_do = 0#32 := by
    rw [written, ← bytesT_four_eq, same]
    exact quiet.clear
  rw [clear]
  rfl

/-- Application can read its accumulator's closure after overwriting stack
slots: the empty-stack payload retains that direct root and frames its object. -/
theorem StackEditOutside.accu_field_load {P : Prog} {s : St} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high i l a k : Nat} {v : Val} {log : List WEntry}
    {memory : Std.ExtHashMap Nat (BitVec 8)}
    (outside : StackEditOutside log P s c pl cp high) (h : VmPayload P s c pl cp sp high)
    (field : FieldSelection s.heap pl s.accu i v l a k)
    (written : memory = writeLog c.σ.mem log) :
    sign_extend (m := 64) (bytesT8 memory (a + 8 * (k + i))) = word c (a + 8 * (k + i)) := by
  have emptyWords : StackRepr c pl high high [] := by
    constructor
    · simp
    · intro j x impossible; simp at impossible
  have empty := payload_stack_of_root h (stack := []) (by intro x impossible; simp at impossible) emptyWords
  exact field.load_frame empty (fun _ loc => Live.root (by simp [roots]) loc) outside.core written

end OCaml.Vm.Sim
