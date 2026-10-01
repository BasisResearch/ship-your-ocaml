import OCaml.Vm.Sim.StackStore

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

/-- Separation for a stack edit: frame the non-stack payload with an empty
stack view, while retaining separation for every originally live object. -/
structure StackEditOutside (log : List WEntry) (P : Prog) (s : St) (c : Config)
    (pl : Place) (cp : ChanPlace) (high : Nat) : Prop where
  core : PayloadOutside log P {s with stack := []} c pl cp high
  heap : ∀ l a o, Live s.heap (roots P s) l → pl.φ l = some a → s.heap.get? l = some o →
    ObjectOutside log a o

/-- Reuse the whole payload frame on the empty-stack view, then supply the
new stack and its live heap. The existing object-copy combinator frames each
retained object; no relocation or machine-run induction is repeated. -/
theorem payload_frame_stack {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp newSp high : Nat} {stack : List Val} {log : List WEntry}
    (h : VmPayload P s c pl cp sp high)
    (outside : StackEditOutside log P s c pl cp high)
    (memory : after.σ.mem = writeLog c.σ.mem log)
    (output : after.σ.sailOutput = c.σ.sailOutput)
    (root : ∀ v ∈ stack, ∀ l, v.loc? = some l → Live s.heap (roots P s) l)
    (words : StackRepr after pl newSp high stack) :
    VmPayload P {s with stack := stack} after pl cp newSp high := by
  have emptyWords : StackRepr c pl high high [] := by
    constructor
    · simp
    · intro i v hi; simp at hi
  have empty := payload_stack_of_root h (stack := []) (by intro v hv; simp at hv) emptyWords
  have framed := empty.frame_log outside.core memory output
  refine { framed with stack := words, heap := ?_ }
  constructor
  · intro l hl
    have oldLive := live_stack_of_root root hl
    obtain ⟨a, o, placed, object, layout⟩ := h.heap.1 l oldLive
    have separate := outside.heap l a o oldLive placed object
    exact ⟨a, o, placed, object, object_copied layout
      (copied_of_writeLog memory separate.header) (copied_of_writeLog memory separate.payload)⟩
  · intro l l' a a' o o' hl hl' ne placed placed' object object'
    exact h.heap.2 l l' a a' o o' (live_stack_of_root root hl)
      (live_stack_of_root root hl') ne placed placed' object object'

/-- ASSIGN changes one existing stack slot. -/
def assignLog (sp i : Nat) (w : BitVec 64) : List WEntry := [(sp + 8 * i, 8, w)]

theorem stack_assign {c after : Config} {pl : Place} {sp high i : Nat}
    {stack : List Val} {v : Val} {w : BitVec 64}
    (h : StackRepr c pl sp high stack) (bound : i < stack.length)
    (value : valWord pl v = some w)
    (memory : after.σ.mem = writeLog c.σ.mem (assignLog sp i w)) :
    StackRepr after pl sp high (stack.set i v) := by
  constructor
  · simpa only [List.length_set] using h.1
  · intro j x hx
    by_cases equal : i = j
    · subst j
      have same : v = x := Option.some.inj (by simpa only [List.getElem?_set_self bound] using hx)
      subst x
      have stored : word after (sp + 8 * i) = w := by
        rw [word, memory]
        exact word_writeLog c.σ.mem (sp + 8 * i) w
      rw [stored]
      exact value
    · have selected : stack[j]? = some x := by simpa only [List.getElem?_set_ne equal] using hx
      have outside : OutLRange (assignLog sp i w) (sp + 8 * j) 8 := by
        simp only [assignLog, OutLRange, and_true]
        omega
      have frame := bytesT_writeLog_out c.σ.mem outside
      change valWord pl x = some (bytesT after.σ.mem (sp + 8 * j) 8)
      rw [memory, frame]
      exact h.2 j x selected

theorem assigned_root {P : Prog} {s : St} {i : Nat} :
    ∀ v ∈ s.stack.set i s.accu, ∀ l, v.loc? = some l → Live s.heap (roots P s) l := by
  intro v member l loc
  rcases List.mem_or_eq_of_mem_set member with member | rfl
  · exact Live.root (by simp [roots, member]) loc
  · exact Live.root (by simp [roots]) loc

/-- Concrete stack update and abstract root update share the common payload frame. -/
theorem payload_stack_assign {P : Prog} {s : St} {c after : Config}
    {pl : Place} {cp : ChanPlace} {sp high i : Nat} {w : BitVec 64}
    (h : VmPayload P s c pl cp sp high) (bound : i < s.stack.length)
    (value : valWord pl s.accu = some w)
    (outside : StackEditOutside (assignLog sp i w) P s c pl cp high)
    (memory : after.σ.mem = writeLog c.σ.mem (assignLog sp i w))
    (output : after.σ.sailOutput = c.σ.sailOutput) :
    VmPayload P {s with stack := s.stack.set i s.accu} after pl cp sp high :=
  payload_frame_stack h outside memory output assigned_root (stack_assign h.stack bound value memory)

end OCaml.Vm.Sim
