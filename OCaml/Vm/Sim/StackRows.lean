import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.InvariantUse
import OCaml.RefinementF1

/-!
# Shared lemmas for unconditional stack rows

From the loop-head invariant `LoopAt`, the dispatch code facts and the
budget's stack bound, a stack-read step is simulated: every premise of a generated
stack-read arm is derived (`ArmInput.of_loop`, the selected stack slot from
the step, its read window from `StackGeometry.read`). The generated rows
(`AccRows.lean`) package one F1 table row (`OpArm`) per opcode.
-/

namespace OCaml.Vm.Sim
set_option autoImplicit false
open OCaml.Bytecode Vsa.Machine Vsa.Sim OCaml.Vm.Primitives

theorem opt_next {α : Type} {o : Option α} {k : α → Res} {s' : St} (h : opt o k = .next s') :
    ∃ a, o = some a ∧ k a = .next s' := by
  cases o with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

/-- A continuation that always steps never halts. -/
theorem opt_not_halt {α : Type} {o : Option α} {k : α → St} {e : Nat} {w : World} :
    opt o (fun a => .next (k a)) ≠ .halt e w := by
  cases o <;> simp [opt]

/-- **The budget's stack capacity**: the budget's stack, plus the
`Stack_threshold` slack that `check_stacks` keeps free (so it never calls
`caml_realloc_stack`), fits in the VM stack allocation. Pushes of up to 256
words then stay inside the allocation. -/
def StackCapacity (B : OCaml.Budget) : Prop :=
  8 * B.stackWords + Layout.stackThresholdBytes ≤ Layout.stackBytes

/-- The budget bounds every reachable stack, plus `k` pushed words, by the
VM stack allocation. -/
theorem stack_fits {B : OCaml.Budget} {P : Prog} {s : St} (fits : OCaml.Fits B P)
    (capacity : StackCapacity B) (reach : Reach P s) {k : Nat}
    (small : 8 * k ≤ Layout.stackThresholdBytes := by decide) :
    8 * (s.stack.length + k) ≤ Layout.stackBytes := by
  have := (fits s reach).1
  unfold StackCapacity at capacity
  omega

/-- **The runtime-framing contract** for VM stack writes: the runtime
invariant pins `Caml_state->stack_high` to `high` (the stack never moves
under the budget) and ignores every write inside the VM stack allocation.
A named obligation on the chosen `Layout`; whoever defines `runtimeOk`
supplies it. -/
structure RuntimeFrame (L : OCaml.Layout) (high : Nat) : Prop where
  stackHigh : ∀ c, L.runtimeOk c →
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high
  stackWindow : ∀ lo hi, high - Layout.stackBytes ≤ lo → hi ≤ high →
    WindowStable L.runtimeOk [⟨lo, hi⟩]

/-- The window of a push of `k` words below `sp` is runtime-stable. -/
theorem RuntimeFrame.push {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high high' k : Nat} (rf : RuntimeFrame L high')
    (h : ArmInput L P s op c pl cp sp high)
    (space : 8 * (s.stack.length + k) ≤ Layout.stackBytes) :
    WindowStable L.runtimeOk [⟨sp - 8 * k, sp⟩] := by
  have same : high = high' := h.stackHigh.symm.trans (rf.stackHigh c h.runtime)
  subst same
  have := h.stack.1
  exact rf.stackWindow _ _ (by omega) (by omega)

/-- **A one-word push is separated and writable**, from the geometry and
the post-push stack bound. -/
theorem PushWriteOk.of_geometry {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {sp high : Nat} {w : BitVec 64} (g : StackGeometry P s c pl cp high)
    (stack : StackRepr c pl sp high s.stack)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes) : PushWriteOk P s c pl cp sp w := by
  have hs := stack.1
  have ht := g.top
  have hg := g.statics
  have hb : 16 ≤ Layout.sym_bss_end := by decide
  have room : high - Layout.stackBytes + 8 * 1 ≤ sp := by omega
  have inside : LogInW [freeWindow sp high] (pushLog sp w) := by
    simp only [pushLog, freeWindow, LogInW, InsideW, or_false, and_true]
    omega
  exact ⟨by omega, by omega, by simpa only [Nat.mul_one] using g.write stack (by decide) room,
    g.payload stack inside, g.image inside, g.bindings stack inside⟩

/-- Shared simulation of a stack read `ACCn` from the loop head. -/
theorem stack_read_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {n : Nat}
    (arm : ∀ pl cp sp high v, ArmInput L P s op c pl cp sp high → s.stack[n]? = some v →
      ReadWindow (BitVec.ofNat 64 (sp + 8 * n)) 8 →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P {s with pc := s.pc + 1, accu := v} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s c op)
    (space : 8 * s.stack.length ≤ Layout.stackBytes)
    (step : opt (s.stack[n]?) (fun v => .next { (s.adv 1) with accu := v }) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  have bound : n < s.stack.length := (List.getElem?_eq_some_iff.mp selected).1
  obtain ⟨c', run, running⟩ := arm pl cp sp high v input selected
    ((input.geometry.read input.stack (stack_space input.stack space) bound).window)
  exact ⟨c', run, h.of_plus run running⟩

/-- Shared simulation of `PUSH`/`PUSHACC0` from the loop head. -/
theorem push_next {L : OCaml.Layout} {P : Prog} {s : St} {c : Config} {op : Opcode}
    {high0 : Nat} (rf : RuntimeFrame L high0)
    (arm : ∀ pl cp sp high w, WindowStable L.runtimeOk [⟨sp - 8, sp⟩] →
      ArmInput L P s op c pl cp sp high → PushWriteOk P s c pl cp sp w →
      valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P
        {s with pc := s.pc + 1, accu := s.accu, stack := s.accu :: s.stack} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s c op)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes) :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P (pushAccu (s.adv 1)) c' := by
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨w, -, pushed⟩ := input.accu
  obtain ⟨c', run, running⟩ := arm pl cp sp high w
    (by simpa only [Nat.mul_one] using rf.push input space) input
    (PushWriteOk.of_geometry input.geometry input.stack space) pushed
  exact ⟨c', run, h.of_plus run running⟩

/-- Shared simulation of `PUSHACCn` (`n ≥ 1`, reading slot `n - 1` of the old stack). -/
theorem push_read_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {n high0 : Nat} (rf : RuntimeFrame L high0)
    (arm : ∀ pl cp sp high w v, WindowStable L.runtimeOk [⟨sp - 8, sp⟩] →
      ArmInput L P s op c pl cp sp high → PushWriteOk P s c pl cp sp w →
      s.stack[n]? = some v → RamReadAt (sp + 8 * n) 8 → valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P
        {s with pc := s.pc + 1, accu := v, stack := s.accu :: s.stack} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s c op)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : opt (s.stack[n]?) (fun v => .next { (pushAccu (s.adv 1)) with accu := v }) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨w, -, pushed⟩ := input.accu
  have bound : n < s.stack.length := (List.getElem?_eq_some_iff.mp selected).1
  obtain ⟨c', run, running⟩ := arm pl cp sp high w v
    (by simpa only [Nat.mul_one] using rf.push input space) input
    (PushWriteOk.of_geometry input.geometry input.stack space) selected
    (input.geometry.read input.stack (stack_space input.stack (by omega)) bound) pushed
  exact ⟨c', run, h.of_plus run running⟩

end OCaml.Vm.Sim
