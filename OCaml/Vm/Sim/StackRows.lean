import OCaml.Vm.Sim.ArmGeometry
import OCaml.Vm.Sim.ArmInput
import OCaml.Vm.Sim.StackStore
import OCaml.Vm.Sim.FieldRead
import OCaml.Vm.Sim.EnterReady
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

/-- **The budget's stack capacity**: the budget's stack, plus twice the
`Stack_threshold` slack, fits in the VM stack allocation. One threshold is
what `check_stacks` keeps free (so it never calls `caml_realloc_stack`), the
other covers the words an arm pushes (at most 256) before its successor's
budget bound applies. -/
def StackCapacity (B : OCaml.Budget) : Prop :=
  8 * B.stackWords + 2 * Layout.stackThresholdBytes ≤ Layout.stackBytes

/-- The budget bounds every reachable stack, plus `k` pushed words and the
threshold slack, by the VM stack allocation. -/
theorem stack_fits_threshold {B : OCaml.Budget} {P : Prog} {s : St} (fits : OCaml.Fits B P)
    (capacity : StackCapacity B) (reach : Reach P s) {k : Nat}
    (small : 8 * k ≤ Layout.stackThresholdBytes := by decide) :
    8 * (s.stack.length + k) + Layout.stackThresholdBytes ≤ Layout.stackBytes := by
  have := (fits s reach).1
  unfold StackCapacity at capacity
  omega

/-- The budget bounds every reachable stack, plus `k` pushed words, by the
VM stack allocation. -/
theorem stack_fits {B : OCaml.Budget} {P : Prog} {s : St} (fits : OCaml.Fits B P)
    (capacity : StackCapacity B) (reach : Reach P s) {k : Nat}
    (small : 8 * k ≤ Layout.stackThresholdBytes := by decide) :
    8 * (s.stack.length + k) ≤ Layout.stackBytes := by
  have := stack_fits_threshold fits capacity reach small
  omega

/-- **The runtime-framing contract**: the runtime invariant pins the
`Caml_state` address and `Caml_state->stack_high` (the stack never moves
under the budget), ignores every write to VM windows, keeps
`stack_threshold` a fixed slack above the stack base, and has no pending
signal at a loop head. A named obligation on the chosen `Layout`, supplied
for F1 by `f1_runtimeFrame` (`F1Frame.lean`). -/
structure RuntimeFrame (L : OCaml.Layout) (high domain : Nat) : Prop where
  domainWord : ∀ c, L.runtimeOk c → (word c Layout.sym_Caml_state).toNat = domain
  stackHigh : ∀ c, L.runtimeOk c →
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_high)).toNat = high
  windows : ∀ ws : List W, (∀ w ∈ ws, VmWindow high domain w) → WindowStable L.runtimeOk ws
  /-- `Caml_state->stack_threshold` stays `Stack_threshold` above the base -/
  threshold : ∀ c, L.runtimeOk c →
    (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_stack_threshold)).toNat =
      high - Layout.stackBytes + Layout.stackThresholdBytes
  /-- no signal or GC request is pending at a loop head (G1: no collection) -/
  quiet : ∀ c, L.runtimeOk c → SignalCheckReady c
  /-- the trap barrier lies at or above the stack top, and backtrace
  recording is off (a raise needs neither) -/
  barrier : ∀ c, L.runtimeOk c →
    high ≤ (word c ((word c Layout.sym_Caml_state).toNat + Layout.off_trap_barrier)).toNat
  backtrace : ∀ c, L.runtimeOk c →
    word c ((word c Layout.sym_Caml_state).toNat + Layout.off_backtrace_active) = 0#64

/-- Every window inside the VM stack allocation is runtime-stable. -/
theorem RuntimeFrame.stackWindow {L : OCaml.Layout} {high domain : Nat} (rf : RuntimeFrame L high domain)
    (lo hi : Nat) (low : high - Layout.stackBytes ≤ lo) (top : hi ≤ high) :
    WindowStable L.runtimeOk [⟨lo, hi⟩] :=
  rf.windows _ fun w hw => by
    simp only [List.mem_singleton] at hw
    subst hw
    exact Or.inl ⟨low, top⟩

/-- The window of a push of `k` words below `sp` is runtime-stable. -/
theorem RuntimeFrame.push {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high high' k dom0 : Nat} (rf : RuntimeFrame L high' dom0)
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
    {sp high : Nat} {w : BitVec 64} (g : ArmGeometry P s c pl cp high)
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
    g.payload stack inside, g.image inside, .of_free g.toStackGeometry stack inside,
    g.bindings stack inside⟩

/-- Shared simulation of a stack read `ACCn` from the loop head. -/
theorem stack_read_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {n : Nat}
    (arm : ∀ pl cp sp high v, ArmInput L P s op c pl cp sp high → s.stack[n]? = some v →
      ReadWindow (BitVec.ofNat 64 (sp + 8 * n)) 8 →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P {s with pc := s.pc + 1, accu := v} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
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
    {high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (arm : ∀ pl cp sp high w, WindowStable L.runtimeOk [⟨sp - 8, sp⟩] →
      ArmInput L P s op c pl cp sp high → PushWriteOk P s c pl cp sp w →
      valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P
        {s with pc := s.pc + 1, accu := s.accu, stack := s.accu :: s.stack} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
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
    {n high0 dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (arm : ∀ pl cp sp high w v, WindowStable L.runtimeOk [⟨sp - 8, sp⟩] →
      ArmInput L P s op c pl cp sp high → PushWriteOk P s c pl cp sp w →
      s.stack[n]? = some v → RamReadAt (sp + 8 * n) 8 → valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P
        {s with pc := s.pc + 1, accu := v, stack := s.accu :: s.stack} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
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

/-- A selected field of a placed block is readable (`heapLow`/`heapArena`). -/
theorem StackGeometry.field_read {P : Prog} {s : St} {c : Config} {pl : Place} {cp : ChanPlace}
    {high i l a k : Nat} {source v : Val} (g : StackGeometry P s c pl cp high)
    (sel : FieldSelection s.heap pl source i v l a k) : RamReadAt (a + 8 * (k + i)) 8 := by
  have found := sel.selected
  rw [sel.pointer] at found
  simp only [field?] at found
  split at found
  · rename_i t fs object
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have lo := g.heapLow l a _ sel.placed object
    have hi := g.heapArena l a _ sel.placed object
    simp only [Obj.wosize] at hi
    refine ⟨?_, ?_, Or.inr ?_⟩ <;> simp only [Layout.sym_bss_end, Layout.sym_tohost,
      Vsa.Sim.DlHeap.heapEnd] at * <;> omega
  · cases found

/-- Shared simulation of a field read into the accumulator (ENVACCn, GETFIELDn). -/
theorem field_read_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {i : Nat} {source : Val} (member : source ∈ roots P s)
    (arm : ∀ pl cp sp high l a k v, ArmInput L P s op c pl cp sp high →
      FieldSelection s.heap pl source i v l a k → RamReadAt (a + 8 * (k + i)) 8 →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P {s with pc := s.pc + 1, accu := v} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (step : opt (field? s.heap source i) (fun v => .next { (s.adv 1) with accu := v }) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt member selected
  obtain ⟨c', run, running⟩ := arm pl cp sp high l a k v input sel (input.geometry.field_read sel)
  exact ⟨c', run, h.of_plus run running⟩

/-- Shared simulation of a field read pushed over the accumulator (PUSHENVACCn). -/
theorem push_field_next {L : OCaml.Layout} {P : Prog} {s s' : St} {c : Config} {op : Opcode}
    {i high0 dom0 : Nat} {source : Val} (rf : RuntimeFrame L high0 dom0) (member : source ∈ roots P s)
    (arm : ∀ pl cp sp high l a k w v, WindowStable L.runtimeOk [⟨sp - 8, sp⟩] →
      ArmInput L P s op c pl cp sp high → PushWriteOk P s c pl cp sp w →
      FieldSelection s.heap pl source i v l a k → RamReadAt (a + 8 * (k + i)) 8 →
      valWord pl s.accu = some w →
      ∃ c', OCaml.Plus c c' ∧ OCaml.Running L P
        {s with pc := s.pc + 1, accu := v, stack := s.accu :: s.stack} c')
    (h : OCaml.LoopAt L P s c) (code : DispatchCode P s op)
    (space : 8 * (s.stack.length + 1) ≤ Layout.stackBytes)
    (step : opt (field? s.heap source i)
      (fun v => .next { (pushAccu (s.adv 1)) with accu := v }) = .next s') :
    ∃ c', OCaml.Plus c c' ∧ OCaml.LoopAt L P s' c' := by
  obtain ⟨v, selected, next⟩ := opt_next step
  cases next
  obtain ⟨pl, cp, sp, high, input⟩ := ArmInput.of_loop h code
  obtain ⟨w, -, pushed⟩ := input.accu
  obtain ⟨l, a, k, sel⟩ := field_selection input.toVmReprAt member selected
  obtain ⟨c', run, running⟩ := arm pl cp sp high l a k w v
    (by simpa only [Nat.mul_one] using rf.push input space) input
    (PushWriteOk.of_geometry input.geometry input.stack space) sel
    (input.geometry.field_read sel) pushed
  exact ⟨c', run, h.of_plus run running⟩

/-- **Closure entry is ready** (`check_stacks` takes its fast path, no signal
is pending) when the frame base `base` stays above `stack_threshold`. -/
theorem RuntimeFrame.enter {L : OCaml.Layout} {P : Prog} {s : St} {op : Opcode} {c : Config}
    {pl : Place} {cp : ChanPlace} {sp high high0 base dom0 : Nat} (rf : RuntimeFrame L high0 dom0)
    (h : ArmInput L P s op c pl cp sp high)
    (room : high - Layout.stackBytes + Layout.stackThresholdBytes ≤ base) : EnterReady c base := by
  have same : high = high0 := h.stackHigh.symm.trans (rf.stackHigh c h.runtime)
  subst same
  have hd := h.geometry.domainArena
  have hl := h.geometry.domainLow
  have off : Layout.off_stack_threshold + 8 ≤ Layout.domainStateBytes := by decide
  refine ⟨rf.quiet c h.runtime, ⟨?_, ?_, Or.inr ?_⟩, ?_⟩
  all_goals first
    | (rw [rf.threshold c h.runtime]; exact room)
    | (simp only [Layout.sym_bss_end, Layout.sym_tohost, Vsa.Sim.DlHeap.heapEnd] at *; omega)

end OCaml.Vm.Sim
